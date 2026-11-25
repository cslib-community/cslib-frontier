/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.Model
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
-- `import all` only to unfold unexposed `MWISInstance.result` into `tablesInst` / `rootPassInst`.
import all CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.Model
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.NodeLayout
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.ProcessNodes
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.RootPass
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Ring

/-!
# End-to-end MWIS Word-RAM runner (`runMWISProg`)

This module composes `initNodesProg`, `processNodesProg`, and `rootPassProg` into the top-level
`Memory.Prog` entry point `runMWISProg`, proves end-to-end validity, output equality with
`MWISInstance.result`, and step-cost bound `inst.stepBound`, and establishes its exact-basis
Word-RAM realization certificate.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.runMWISProg`: top-level Word-RAM dynamic program for
  `MWISInstance`.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.runMWISProg_spec`: end-to-end validity, output
  equality with `MWISInstance.result`, and `memoryCost ≤ inst.stepBound`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.runMWISProg_realizes`: exact-basis Word-RAM
  realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private theorem rp_cost_poly_le {b0 M : ℕ} (h0 : b0 ≤ M) :
    b0 * (2 * b0 + 1) + b0 * 2 + 1 ≤ 5 * M ^ 2 + 5 * M + 17 := by
  nlinarith

private theorem total_stepBound_le {n M cInit cProc cRp : ℕ} (hP : 1 ≤ 2 ^ M)
    (h1 : cInit ≤ 1 + (n + 1) * (2 ^ M + M + 6))
    (h2 : cProc ≤ n * (10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)))
    (h3 : cRp ≤ 2 ^ M * (5 * M ^ 2 + 5 * M + 17)) :
    1 + (1 + (cInit + (cProc + (1 + (1 + (1 + (1 + cRp))))))) ≤
      6 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 32)) := by
  have hInit' : (n + 1) * (2 ^ M + M + 6) ≤ (n + 1) * (2 ^ M * (M + 7)) :=
    Nat.mul_le_mul_left (n + 1) (by nlinarith)
  have hProc' : n * (10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)) ≤
      n * (2 ^ M * (5 * M ^ 2 + 5 * M + 17)) :=
    Nat.mul_le_mul_left n (by nlinarith)
  have h8 : 1 ≤ (n + 1) * (2 ^ M * 8) := by nlinarith
  calc 1 + (1 + (cInit + (cProc + (1 + (1 + (1 + (1 + cRp)))))))
      ≤ 1 + (1 + ((1 + (n + 1) * (2 ^ M * (M + 7))) +
          (n * (2 ^ M * (5 * M ^ 2 + 5 * M + 17)) +
            (1 + (1 + (1 + (1 + 2 ^ M * (5 * M ^ 2 + 5 * M + 17)))))))) := by omega
    _ = 7 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 24)) := by ring
    _ ≤ 6 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 32)) := by linarith

/-- Top-level Word-RAM dynamic program parsing `MWISInstance.encode` at `Memory.State.init`,
processing all `n` nonroot nodes bottom-up, and maximizing over the root bag. -/
def runMWISProg (_ : Unit) : Memory.Prog ℕ := do
  let m ← Memory.read 1
  let n ← Memory.read 2
  let wtPtr := 3
  let adjPtr := 3 + m
  let parPtr := adjPtr + m * m
  let rawBagsPtr := parPtr + (n + 1)
  let descBase ← initNodesProg ⟨rawBagsPtr, n + 1⟩
  let _ ← processNodesProg ⟨m, adjPtr, wtPtr, parPtr, descBase, n⟩
  let bag0Ptr ← Memory.read descBase
  let bag0Len ← Memory.read (descBase + 1)
  let tbl0Ptr ← Memory.read (descBase + 2)
  let tbl0Len ← Memory.read (descBase + 3)
  rootPassProg ⟨m, adjPtr, wtPtr, bag0Ptr, bag0Len, tbl0Ptr, tbl0Len⟩

private theorem init_decode (inst : MWISInstance) :
    (Memory.State.init inst.encode).frontier = inst.encode.length + 1 ∧
    3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) +
      (inst.bags.flatMap encodeBag).length = (Memory.State.init inst.encode).frontier ∧
    (Memory.State.init inst.encode).mem 1 = inst.numVerts ∧
    (Memory.State.init inst.encode).mem 2 = inst.numNodes ∧
    HoldsIn 3 inst.weights (Memory.State.init inst.encode) ∧
    HoldsIn (3 + inst.numVerts) inst.adjMatrix (Memory.State.init inst.encode) ∧
    HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts) inst.parents
      (Memory.State.init inst.encode) ∧
    HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1))
      (inst.bags.flatMap encodeBag) (Memory.State.init inst.encode) := by
  let s₀ := Memory.State.init inst.encode
  have hfr : s₀.frontier = inst.encode.length + 1 := by
    simp [s₀, Memory.State.init, Nat.add_comm]
  have hall : HoldsIn 1 inst.encode s₀ := holdsIn_init inst.encode
  simp only [MWISInstance.encode, List.cons_append, List.nil_append, List.append_assoc] at hall
  rw [HoldsIn.cons_iff] at hall
  obtain ⟨_, hm1, hall⟩ := hall
  rw [HoldsIn.cons_iff] at hall
  obtain ⟨_, hm2, hall⟩ := hall
  rw [HoldsIn.append_iff, inst.weights_len] at hall
  obtain ⟨hwt, hall⟩ := hall
  rw [HoldsIn.append_iff, inst.adjMatrix_len] at hall
  obtain ⟨hadj, hall⟩ := hall
  rw [HoldsIn.append_iff, inst.parents_len] at hall
  obtain ⟨hpar, hbags⟩ := hall
  have hlen_eq : 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) +
      (inst.bags.flatMap encodeBag).length = s₀.frontier := by
    rw [hfr]
    simp only [MWISInstance.encode, List.length_append, List.length_cons, List.length_nil,
      inst.weights_len, inst.adjMatrix_len, inst.parents_len]; omega
  exact ⟨hfr, hlen_eq, hm1, hm2, hwt, hadj, hpar, hbags⟩

/-- End-to-end validity, output equality with `inst.result`, and `memoryCost ≤ inst.stepBound` for
`runMWISProg`. -/
theorem runMWISProg_spec {w : ℕ} (inst : MWISInstance)
    (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runMWISProg ())) ∧
    (Memory.spec 0).clientResult s₀ (runMWISProg ()) = inst.result ∧
    memoryCost (runMWISProg ()) s₀ ≤ inst.stepBound := by
  let s₀ := Memory.State.init inst.encode
  let m := inst.numVerts
  let n := inst.numNodes
  let M := inst.maxBagLen
  obtain ⟨hfr₀, hlen₀, hm1, hm2, hwt₀, hadj₀, hpar₀, hbags₀⟩ := init_decode inst
  have hpow_12 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen ≤
      (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen :=
    Nat.mul_le_mul_right _ (by omega)
  have hfit_init_peak : Fits w (s₀.frontier + 4 * (n + 1) + (n + 1) * 2 ^ M) := hw.of_le (by
    dsimp only [s₀, n, M]
    rw [hfr₀]
    simp only [MWISInstance.wordBound]; omega)
  have hfit_raw : Fits w s₀.frontier := hfit_init_peak.of_le (by omega)
  obtain ⟨hv_init, _, hfr₁, hlay₁, hc_init⟩ :=
    initNodesProg_spec (w := w) inst hwt₀ hadj₀ hpar₀ hbags₀ hfit_init_peak hfit_raw
  let rawBagsPtr := 3 + m + m * m + (n + 1)
  let s₁ := (Memory.spec 0).clientState s₀ (initNodesProg ⟨rawBagsPtr, n + 1⟩)
  let descBase := (Memory.spec 0).clientResult s₀ (initNodesProg ⟨rawBagsPtr, n + 1⟩)
  have hfr₁' : s₁.frontier ≤ inst.encode.length + 1 + 4 * (n + 1) + (n + 1) * 2 ^ M := by
    dsimp only [s₁, rawBagsPtr, m, n, M, s₀] at hfr₁ ⊢; omega
  have h2n1 : (n + 1) * 2 ^ M + n * 2 ^ M = (2 * n + 1) * 2 ^ M := by ring
  have hfit_proc_peak : Fits w (s₁.frontier + n * 2 ^ M) := hw.of_le (by
    dsimp only [n, M] at hfr₁' h2n1 ⊢
    simp only [MWISInstance.wordBound]; omega)
  have hfit_val : Fits w ((n + 1) * M * inst.maxWeight) := hw.of_le (by
    dsimp only [n, M]
    simp only [MWISInstance.wordBound]; omega)
  obtain ⟨hv_proc, _, ⟨tblFinal, hlay₂, _, hagree₂⟩, hc_proc⟩ :=
    processNodesProg_spec (w := w) inst descBase hlay₁ hfit_proc_peak hfit_val
  let procArgs : ProcessNodesArgs := ⟨m, 3 + m, 3, 3 + m + m * m, descBase, n⟩
  let s₂ := (Memory.spec 0).clientState s₁ (processNodesProg procArgs)
  let zeroFin : Fin (n + 1) := 0
  obtain ⟨h0_len, h0_pow, _, h0_bag⟩ := hlay₂.bags_holds zeroFin
  obtain ⟨h0_tlen, _, h0_tbl⟩ := hlay₂.tbl_holds zeroFin
  simp only [zeroFin, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
    at h0_len h0_pow h0_bag h0_tlen h0_tbl
  change HoldsIn (s₂.mem descBase) (inst.bagAt zeroFin) s₂ at h0_bag
  change HoldsIn (s₂.mem (descBase + 2)) (tblFinal zeroFin) s₂ at h0_tbl
  let rpArgs : RootPassArgs :=
    ⟨m, 3 + m, 3, s₂.mem descBase, s₂.mem (descBase + 1),
      s₂.mem (descBase + 2), s₂.mem (descBase + 3)⟩
  obtain ⟨hv_rp, _, hr_rp, hc_rp⟩ := rootPassProg_spec (w := w) rpArgs (inst := inst)
    (L0 := inst.bagAt zeroFin) (tbl0 := tblFinal zeroFin)
    (arr0 := (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[zeroFin]) (s := s₂)
    hlay₂.adj_holds hlay₂.wt_holds rfl h0_bag h0_len.symm (inst.bagAt_mem_lt zeroFin)
    h0_tbl (by dsimp only [rpArgs]; rwa [h0_pow])
    (by
      dsimp only [rpArgs]
      rw [h0_pow]; exact hagree₂ zeroFin)
  have hd_lt (off : ℕ) (hoff : off < 4) : descBase + off < s₂.frontier := by
    have hdesc : descBase + 4 * (n + 1) ≤ s₂.frontier := hlay₂.desc_hi
    omega
  have hr_st (s : Memory.State) (a : ℕ) : (Memory.spec 0).clientState s (Memory.read a) = s := rfl
  have hr_res (s : Memory.State) (a : ℕ) :
      (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold runMWISProg
    dsimp only
    refine validHistory_read_bind (by omega) ?_
    rw [show s₀.mem 1 = m from hm1]
    refine validHistory_read_bind (by omega) ?_
    rw [show s₀.mem 2 = n from hm2]
    refine validHistory_bind_step hv_init (validHistory_bind_step hv_proc ?_)
    refine validHistory_read_bind (by simpa only [Nat.add_zero] using hd_lt 0 (by decide)) ?_
    refine validHistory_read_bind (hd_lt 1 (by decide)) ?_
    refine validHistory_read_bind (hd_lt 2 (by decide)) ?_
    exact validHistory_read_bind (hd_lt 3 (by decide)) hv_rp
  · unfold runMWISProg
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, show s₀.mem 1 = m from hm1,
      StateTransitionSpec.clientResult_bind, hr_st, hr_res, show s₀.mem 2 = n from hm2,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₂ (Memory.read descBase >>= _) = inst.result
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res]
    rw [hr_rp]
    dsimp only [rpArgs, MWISInstance.result]
    rw [h0_pow]
  · unfold runMWISProg
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, show s₀.mem 1 = m from hm1,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, show s₀.mem 2 = n from hm2,
      memoryCost_bind', memoryCost_bind']
    change 1 + (1 + (memoryCost (initNodesProg ⟨rawBagsPtr, n + 1⟩) s₀ +
      (memoryCost (processNodesProg procArgs) s₁ +
        memoryCost (Memory.read descBase >>= _) s₂))) ≤ inst.stepBound
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_st, hr_res]
    have h0_len_le : (inst.bagAt zeroFin).length ≤ M := inst.bagAt_length_le zeroFin
    have hc_rp_M : memoryCost (rootPassProg rpArgs) s₂ ≤ 2 ^ M * (5 * M ^ 2 + 5 * M + 17) :=
      hc_rp.trans (by
        dsimp only [rpArgs]
        rw [h0_len, h0_pow]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) h0_len_le)
          (rp_cost_poly_le h0_len_le))
    dsimp only [s₀, s₁, descBase, rawBagsPtr, procArgs, rpArgs, m, n, M,
      MWISInstance.stepBound] at hc_init hc_proc hc_rp_M ⊢
    exact total_stepBound_le (Nat.one_le_pow M 2 (by decide)) hc_init hc_proc hc_rp_M

private theorem runMWISProg_init_helper {w : ℕ} (inst : MWISInstance)
    (hw : Fits w inst.wordBound) :
    let descBase := 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1)
    let prog := initNodesProg ⟨descBase, inst.numNodes + 1⟩
    let s₀ := Memory.State.init inst.encode
    let s₁ := (Memory.spec 0).clientState s₀ prog
    let descRes := (Memory.spec 0).clientResult s₀ prog
    descRes = s₀.frontier ∧
    s₁.frontier ≤ inst.encode.length + 1 + 4 * (inst.numNodes + 1) +
      (inst.numNodes + 1) * 2 ^ inst.maxBagLen ∧
    NodeLayout inst descRes
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) s₁ := by
  obtain ⟨hfr₀, _, _, _, hwt₀, hadj₀, hpar₀, hbags₀⟩ := init_decode inst
  have hpow_12 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen ≤
      (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen :=
    Nat.mul_le_mul_right _ (by omega)
  have hfit_init_peak : Fits w ((Memory.State.init inst.encode).frontier +
      4 * (inst.numNodes + 1) + (inst.numNodes + 1) * 2 ^ inst.maxBagLen) := hw.of_le (by
    rw [hfr₀]
    simp only [MWISInstance.wordBound]; omega)
  have hfit_raw : Fits w (Memory.State.init inst.encode).frontier := hfit_init_peak.of_le (by omega)
  obtain ⟨_, hdesc_eq, hfr₁, hlay₁, _⟩ :=
    initNodesProg_spec (w := w) inst hwt₀ hadj₀ hpar₀ hbags₀ hfit_init_peak hfit_raw
  refine ⟨hdesc_eq, ?_, hlay₁⟩
  simpa only [hfr₀] using hfr₁

/-- Exact-basis Word-RAM realization certificate for `runMWISProg`. -/
theorem runMWISProg_realizes :
    Realizes .exact runMWISProg WordEncoding.encode WordEncoding.encode
      (fun w _ s =>
        ∃ inst : MWISInstance,
          s = Memory.State.init inst.encode ∧
          Fits w inst.wordBound)
      (fun _ _ => 0) := by
  unfold runMWISProg
  realize [initNodesProg_realizes, processNodesProg_realizes, rootPassProg_realizes]
  all_goals
    obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨hfr₀, _, hm1, hm2, _, _, _, hbags₀⟩ := init_decode inst
    try rw [hm1]
    try rw [hm2]
  all_goals try exact hw.of_le (by simp only [MWISInstance.wordBound]; omega)
  · have hpow_12 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen ≤
        (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen := Nat.mul_le_mul_right _ (by omega)
    exact ⟨inst.bags, inst.maxBagLen, inst.bags_len,
      fun B hB => List.mem_le_foldl_max (List.mem_map_of_mem hB), hbags₀,
      hw.of_le (by
        rw [hfr₀]
        simp only [MWISInstance.wordBound]; omega)⟩
  · obtain ⟨_, hfr₁', hlay₁⟩ := runMWISProg_init_helper inst hw
    refine ⟨inst, fun i => List.replicate (2 ^ (inst.bagAt i).length) 0,
      rfl, rfl, rfl, rfl, hlay₁, prefixMaxSum_replicate_zero _ _, hw.of_le ?_,
      hw.of_le (by simp only [MWISInstance.wordBound]; omega)⟩
    have : (inst.numNodes + 1) * 2 ^ inst.maxBagLen + inst.numNodes * 2 ^ inst.maxBagLen =
        (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen := by ring
    simp only [MWISInstance.wordBound]; omega
  all_goals
    obtain ⟨hdesc_eq, hfr₁', hlay₁⟩ := runMWISProg_init_helper inst hw
  all_goals try
    (change (Memory.spec 0).clientResult _ _ = _ at hdesc_eq
     rw [hdesc_eq, hfr₀]
     exact hw.of_le (by simp only [MWISInstance.wordBound]; omega))
  · let initProg := initNodesProg
      ⟨3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1), inst.numNodes + 1⟩
    let s₁ := (Memory.spec 0).clientState (Memory.State.init inst.encode) initProg
    let descRes := (Memory.spec 0).clientResult (Memory.State.init inst.encode) initProg
    have h2n1 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen + inst.numNodes * 2 ^ inst.maxBagLen =
        (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen := by ring
    have hfit_proc_peak : Fits w (s₁.frontier + inst.numNodes * 2 ^ inst.maxBagLen) := hw.of_le (by
      dsimp only [s₁, initProg] at hfr₁' ⊢
      simp only [MWISInstance.wordBound]; omega)
    have hfit_val : Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight) := hw.of_le (by
      simp only [MWISInstance.wordBound]; omega)
    obtain ⟨_, hfr₂, ⟨tblFinal, hlay₂, hpfx₂, _⟩, _⟩ :=
      processNodesProg_spec (w := w) inst descRes hlay₁ hfit_proc_peak hfit_val
    have hfr₂_bound : ((Memory.spec 0).clientState s₁
        (processNodesProg ⟨inst.numVerts, 3 + inst.numVerts, 3,
          3 + inst.numVerts + inst.numVerts * inst.numVerts, descRes, inst.numNodes⟩)).frontier ≤
        inst.wordBound := by
      dsimp only [s₁, initProg, descRes] at hfr₁' hfr₂ ⊢
      simp only [MWISInstance.wordBound]; omega
    dsimp only [s₁, initProg, descRes] at hfr₂_bound hlay₂
    let zeroFin : Fin (inst.numNodes + 1) := 0
    obtain ⟨h0_len, h0_pow, _, h0_bag⟩ := hlay₂.bags_holds zeroFin
    obtain ⟨h0_tlen, _, h0_tbl⟩ := hlay₂.tbl_holds zeroFin
    simp only [zeroFin, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
      at h0_len h0_pow h0_bag h0_tlen h0_tbl
    have hmax0 : (tblFinal zeroFin).foldl max 0 ≤
        inst.numNodes * (inst.maxBagLen * inst.maxWeight) :=
      (foldl_max_le_prefixMaxSum tblFinal zeroFin (Nat.zero_le _)).trans hpfx₂
    have h0_len_le : (inst.bagAt zeroFin).length ≤ inst.maxBagLen := inst.bagAt_length_le zeroFin
    have hcap_root : (inst.bagAt zeroFin).length * inst.weights.foldl max 0 +
        (tblFinal zeroFin).foldl max 0 ≤
        (inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight := by
      calc (inst.bagAt zeroFin).length * inst.weights.foldl max 0 + (tblFinal zeroFin).foldl max 0
          ≤ inst.maxBagLen * inst.maxWeight +
              inst.numNodes * (inst.maxBagLen * inst.maxWeight) :=
            Nat.add_le_add (Nat.mul_le_mul_right _ h0_len_le) hmax0
        _ = (inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight := by ring
    exact ⟨inst.numVerts, inst.adjMatrix, inst.weights, inst.bagAt zeroFin, tblFinal zeroFin,
      (inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight,
      inst.adjMatrix_len, inst.weights_len, rfl,
      hlay₂.adj_holds, hlay₂.wt_holds,
      h0_bag, h0_len.symm, inst.bagAt_mem_lt zeroFin,
      h0_tbl, by rwa [h0_pow], by rwa [h0_len],
      hw.of_le (by have := inst.adjMatrix_len ▸ hlay₂.adj_holds.1; omega),
      hw.of_le (by have := inst.weights_len ▸ hlay₂.wt_holds.1; omega),
      hw.of_le (by have := h0_len ▸ h0_bag.1; omega),
      hw.of_le (by
        have := h0_tbl.1
        rw [h0_pow, ← h0_tlen]; omega),
      hfit_val⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
