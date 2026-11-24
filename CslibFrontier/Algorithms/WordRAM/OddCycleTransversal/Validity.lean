/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.CompressProg
import Mathlib.Tactic.Linarith

/-!
# History admissibility (`ValidHistory`) for `octProg`

This module certifies `Memory.spec w` history admissibility (`ValidHistory`) across all subroutines
(`readSplitCap`, `readResCap`, `bfsProg`, `minSepProg`, `buildWProg`, `leafProg`, `compressProg`,
and `octProg`). It builds in parallel with `Cost`, `MinSep`, and `LeafSubroutines`.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.inputFits_encodeInput`: `InputFits` certificate for
  `encodeInput G k`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.validHistory_octProg`: memory-safety history
  validity of `octProg ()` from `Memory.State.init (encodeInput G k)`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write clientState_map

private theorem validHistory_readSplitCap {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readSplitCap d)) := by
  rcases d with ⟨⟨⟨n, m⟩, x⟩, y⟩
  have hfr := hs.2
  dsimp only [octWorkspace] at hfr
  unfold readSplitCap
  dsimp only [SplitNetArgs.n, SplitNetArgs.m, SplitNetArgs.arg1]
  refine validHistory_read_bind (by omega) ?_
  split_ifs
  all_goals
    first
    | exact validHistory_pure _ _ _
    | (refine validHistory_read_bind ?_ ?_
       · dsimp only [splitCount, keepBase, flipBase, wBase] at *
         first
         | omega
         | (have hu : x - (n + 2) < n := by omega
            have hmul : (x - (n + 2)) * n < n * n := Nat.mul_lt_mul_of_pos_right hu (by omega)
            omega)
       · exact validHistory_ite (fun _ => validHistory_pure _ _ _)
           (fun _ => validHistory_pure _ _ _))

private theorem validHistory_readResCap {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w d.1.1.1 s) (hx : d.1.2 < splitCount d.1.1.1) (hy : d.2 < splitCount d.1.1.1) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readResCap d)) := by
  rcases d with ⟨⟨⟨n, m⟩, x⟩, y⟩
  dsimp only at hs hx hy
  unfold readResCap
  refine validHistory_bind_step (validHistory_readSplitCap hs) ?_
  rw [clientState_readSplitCap]
  dsimp only
  have hfr := hs.2
  have hsq := splitCount_sq n
  have h1 : flowBase n + x * splitCount n + y < s.frontier := by
    have hlt : x * splitCount n + y < splitCount n * splitCount n := by nlinarith
    dsimp only [octWorkspace, flowBase, splitCount] at hfr hlt ⊢
    omega
  have h2 : flowBase n + y * splitCount n + x < s.frontier := by
    have hlt : y * splitCount n + x < splitCount n * splitCount n := by nlinarith
    dsimp only [octWorkspace, flowBase, splitCount] at hfr hlt ⊢
    omega
  exact validHistory_read_bind h1 (validHistory_read_bind h2
    (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)))

private theorem validHistory_bfsProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bfsProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hs
  have hsq := splitCount_sq n
  unfold bfsProg
  dsimp only
  have hfill : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fillRange ((distBase n, splitCount n), splitCount n))) :=
    validHistory_fillRange hs
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount]; omega)
      (by apply hw.of_le; dsimp only [octWorkspace, splitCount]; omega)
  refine validHistory_bind_step hfill ?_
  have hs1 := MonotoneMemInv.pres hs hfill
  refine validHistory_write_bind
    (by have := hs1.2; dsimp only [octWorkspace, distBase, flowBase, splitCount] at *; omega)
    (fits_zero w) ?_
  refine validHistory_write_bind
    (by have := hs1.2; dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at *;
        omega)
    (fits_zero w) ?_
  have hs2 := memReady_write (memReady_write hs1 (distBase n) 0 (fits_zero w))
    (parBase n) 0 (fits_zero w)
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n - 1) 0
      (fun layer hlayer t ht => ⟨?_, ?_⟩) hs2)
    (validHistory_pure _ _ _)
  · unfold bfsLayerStep
    dsimp only [GraphStepArgs.n, GraphStepArgs.m]
    refine validHistory_read_bind
      (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n) 0
        (fun u hu t' ht' => ⟨?_, ?_⟩) ht)
      (validHistory_pure _ _ _)
    · unfold bfsMidStep
      dsimp only [SplitNetArgs.n, SplitNetArgs.m, SplitNetArgs.arg1]
      refine validHistory_read_bind
        (by have := ht'.2
            dsimp only [octWorkspace, distBase, flowBase, splitCount] at hu this ⊢; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n) 0
          (fun v hv t'' ht'' => ⟨?_, ?_⟩) ht')
        (validHistory_pure _ _ _)
      · unfold bfsInnerStep
        dsimp only [BfsInnerArgs.n, BfsInnerArgs.m, BfsInnerArgs.layer, BfsInnerArgs.u]
        have hdv : distBase n + v < t''.frontier := by
          have := ht''.2
          dsimp only [octWorkspace, distBase, flowBase, splitCount] at hv this ⊢; omega
        refine validHistory_read_bind hdv ?_
        have hrc := validHistory_readResCap (d := (((n, m), u), v)) ht''
          (by dsimp only; omega) (by dsimp only; omega)
        refine validHistory_bind_step hrc ?_
        have ht3 := MonotoneMemInv.pres ht'' hrc
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_write_bind
          (by have := ht3.2
              dsimp only [octWorkspace, distBase, flowBase, splitCount] at hv this ⊢; omega)
          (by apply hw.of_le; dsimp only [octWorkspace, splitCount] at hlayer ⊢; omega) ?_
        exact validHistory_write_bind
          (by have := ht3.2
              dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hv this ⊢
              omega)
          (by apply hw.of_le; dsimp only [octWorkspace, splitCount] at hu ⊢; omega)
          (validHistory_pure _ _ _)
      · exact clientResult_bfsInnerStep _ t''
    · exact clientResult_bfsMidStep _ t'
  · unfold bfsLayerStep; simp only [client_simps]

private theorem validHistory_minSepProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (minSepProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hs
  have hsq := splitCount_sq n
  unfold minSepProg
  dsimp only
  have hfill := validHistory_fillRange (d := ((flowBase n, 0), splitCount n * splitCount n))
    hs (by dsimp only [octWorkspace, flowBase, splitCount]; omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  have hs1 := MonotoneMemInv.pres hs hfill
  have haug := validHistory_iterate_inv (MemReady w n) augRoundStep (n, m)
    (fun r t ht => by
      unfold augRoundStep
      dsimp only [GraphStepArgs.n, GraphStepArgs.m]
      have hbfs := validHistory_bfsProg (d := (n, m)) hw ht
      refine validHistory_bind_step hbfs ?_
      have ht1 := MonotoneMemInv.pres ht hbfs
      refine validHistory_read_bind
        (by have := ht1.2
            dsimp only [octWorkspace, distBase, flowBase, splitCount] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_inv (MemReady w n) pushUnitStep n (fun cur t' ht' => ?_) _ 1 ht1)
        (validHistory_pure _ _ _)
      unfold pushUnitStep
      dsimp only
      refine validHistory_read_bind (by have := ht'.2; dsimp only [octWorkspace] at *; omega) ?_
      refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_read_bind
        (by have := ht'.2
            dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hcur this ⊢
            omega)
        ?_
      refine validHistory_ite (fun hu => ?_) (fun _ => validHistory_pure _ _ _)
      have had1 : flowBase n + cur * splitCount n +
          t'.mem (parBase n + cur) < t'.frontier := by
        have hlt : cur * splitCount n + t'.mem (parBase n + cur) <
            splitCount n * splitCount n := by nlinarith
        have := ht'.2
        dsimp only [octWorkspace, flowBase, splitCount] at hlt this ⊢; omega
      have had2 : flowBase n + t'.mem (parBase n + cur) * splitCount n +
          cur < t'.frontier := by
        have hlt : t'.mem (parBase n + cur) * splitCount n + cur <
            splitCount n * splitCount n := by nlinarith
        have := ht'.2
        dsimp only [octWorkspace, flowBase, splitCount] at hlt this ⊢; omega
      refine validHistory_read_bind had1 ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
      · exact validHistory_write_bind had1 ((ht'.1.mem_fits _).of_le (Nat.sub_le _ _))
          (validHistory_pure _ _ _)
      · refine validHistory_read_bind had2 ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        exact validHistory_write_bind had2
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
    n 0 hs1
  refine validHistory_bind_step haug ?_
  have hs2 := MonotoneMemInv.pres hs1 haug
  have hbfs2 := validHistory_bfsProg (d := (n, m)) hw hs2
  refine validHistory_bind_step hbfs2 ?_
  have hs3 := MonotoneMemInv.pres hs2 hbfs2
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := MemReady w n) n 0 0
      (fun v hv cnt t ht => ⟨?_, ?_⟩) hs3)
    (validHistory_pure _ _ _)
  · unfold extractSepStep
    dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
    have hfr := ht.2
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, wBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr hv ⊢; omega) ?_
    have hsep : sepOutBase n + v < t.frontier := by
      dsimp only [octWorkspace, sepOutBase, parBase, distBase, flowBase, splitCount] at hfr hv ⊢
      omega
    exact validHistory_ite
      (fun _ => validHistory_write_bind hsep
        (by apply hw.of_le; dsimp only [octWorkspace]; omega) (validHistory_pure _ _ _))
      (fun _ => validHistory_write_bind hsep (fits_zero w) (validHistory_pure _ _ _))
  · exact (clientResult_extractSepStep _ t).1

private theorem validHistory_buildWProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hm : d.2 < d.1) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (buildWProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hm hs
  unfold buildWProg
  dsimp only
  have hcp := validHistory_copyRange (d := ((sepBase n, wBase n), n)) hs
    (by dsimp only [octWorkspace, sepBase]; omega)
    (by dsimp only [octWorkspace, wBase]; omega)
  refine validHistory_bind_step hcp ?_
  have hs1 := MonotoneMemInv.pres hs hcp
  have hwm : wBase n + m <
      ((Memory.spec 0).clientState s (copyRange ((sepBase n, wBase n), n))).frontier := by
    have := hs1.2; dsimp only [octWorkspace, wBase] at *; omega
  have h1 : Fits w 1 := by apply hw.of_le; dsimp only [octWorkspace]; omega
  refine validHistory_write_bind hwm h1 ?_
  have hs2 := memReady_write hs1 (wBase n + m) 1 h1
  have hloop : ∀ rem vL t, vL.1 + rem = n → vL.2 ≤ vL.1 → MemReady w n t →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate buildWListStep n rem vL)) := by
    intro rem
    induction rem with
    | zero => intro vL t _ _ _; exact validHistory_pure _ _ _
    | succ rem ih =>
      intro vL t hsum hL ht
      have hvstep : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (buildWListStep (n, vL))) := by
        unfold buildWListStep
        dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
        refine validHistory_read_bind
          (by have := ht.2; dsimp only [octWorkspace, wBase] at *; omega) ?_
        exact validHistory_ite
          (fun _ => validHistory_write_bind
            (by have := ht.2; dsimp only [octWorkspace, wListBase] at *; omega)
            (by apply hw.of_le; dsimp only [octWorkspace]; omega)
            (validHistory_pure _ _ _))
          (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step hvstep ?_
      have ht' := MonotoneMemInv.pres ht hvstep
      refine ih _ _ ?_ ?_ ht'
      · obtain ⟨h1, _⟩ := clientResult_buildWListStep (n, vL) t
        dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at h1; omega
      · obtain ⟨h1, h2⟩ := clientResult_buildWListStep (n, vL) t
        dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at h1 h2; omega
  exact validHistory_bind_step (hloop n (0, 0) _ (Nat.zero_add _) le_rfl hs2)
    (validHistory_pure _ _ _)

private theorem validHistory_leafProg {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1.1.1)) (hL : d.2 ≤ d.1.1.1) (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (leafProg d)) := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hw hL hs
  have h1 : Fits w 1 := by apply hw.of_le; dsimp only [octWorkspace]; omega
  unfold leafProg
  dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
  have hunpack : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (unpackGuessProg (n, L))) := by
    unfold unpackGuessProg
    dsimp only
    have hf := validHistory_fillRange (d := ((guessBase n, 0), n)) hs
      (by dsimp only [octWorkspace, guessBase]; omega) (fits_zero w)
    refine validHistory_bind_step hf ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := MemReady w n) L 0 (fun j hj t ht => ⟨?_, ?_⟩)
        (MonotoneMemInv.pres hs hf))
      (validHistory_pure _ _ _)
    · unfold unpackStep
      dsimp only
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
      exact validHistory_ite
        (fun hcond => validHistory_write_bind
          (by have := ht.2; dsimp only [octWorkspace, guessBase] at *; omega)
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_pure _ _ _)
    · exact clientResult_unpackStep _ t
  refine validHistory_bind_ready hs hunpack fun _ t1 hs1 => ?_
  refine validHistory_bind_ready hs1 ?_ fun _ t2 hs2 => ?_
  · unfold checkProperProg
    dsimp only
    refine validHistory_read_bind (by have := hs1.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_fst (Inv := MemReady w n) L 0 1 (fun i hi ok t ht => ⟨?_, ?_⟩) hs1)
      (validHistory_pure _ _ _)
    · unfold properOuterStep
      dsimp only [ProperOuterArgs.n, ProperOuterArgs.m, ProperOuterArgs.L,
        ProperOuterArgs.i, ProperOuterArgs.ok]
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_fst (Inv := MemReady w n) L 0 ok (fun j hj ok' t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold properInnerStep
        dsimp only [ProperInnerArgs.n, ProperInnerArgs.m, ProperInnerArgs.u,
          ProperInnerArgs.du, ProperInnerArgs.j, ProperInnerArgs.ok]
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
        refine validHistory_ite (fun hcond => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_read_bind ?_
          (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _))
        have := ht'.2
        have hmul : t.mem (wListBase n + i) * n < n * n :=
          Nat.mul_lt_mul_of_pos_right hcond.1 (by omega)
        dsimp only [octWorkspace] at this ⊢; omega
      · exact clientResult_properInnerStep_fst _ t'
    · exact clientResult_properOuterStep_fst _ t
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_ready hs2 ?_ fun _ t3 hs3 => ?_
  · unfold buildTerminalsProg
    dsimp only [GraphStepArgs.n]
    have hf1 := validHistory_fillRange (d := ((keepBase n, 0), n)) hs2
      (by dsimp only [octWorkspace, keepBase]; omega) (fits_zero w)
    refine validHistory_bind_step hf1 ?_
    have hs2a := MonotoneMemInv.pres hs2 hf1
    have hf2 := validHistory_fillRange (d := ((flipBase n, 0), n)) hs2a
      (by dsimp only [octWorkspace, flipBase]; omega) (fits_zero w)
    refine validHistory_bind_step hf2 ?_
    have hs2b := MonotoneMemInv.pres hs2a hf2
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := MemReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs2b)
      (validHistory_pure _ _ _)
    · unfold termOuterStep
      dsimp only [TermOuterArgs.n, TermOuterArgs.m, TermOuterArgs.L]
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, wBase] at *; omega) ?_
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, colBase] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := MemReady w n) L 0 (fun j hj t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold termInnerStep
        dsimp only [TermInnerArgs.n, TermInnerArgs.m, TermInnerArgs.v, TermInnerArgs.cv]
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
        refine validHistory_ite (fun hcond => ?_) (fun _ => validHistory_pure _ _ _)
        have hadj : 3 + t'.mem (wListBase n + j) * n + v < t'.frontier := by
          have := ht'.2
          have hmul : t'.mem (wListBase n + j) * n < n * n :=
            Nat.mul_lt_mul_of_pos_right hcond.1 (by omega)
          dsimp only [octWorkspace] at this ⊢; omega
        refine validHistory_read_bind hadj ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        exact validHistory_ite
          (fun _ => validHistory_write_bind
            (by have := ht'.2; dsimp only [octWorkspace, flipBase] at *; omega) h1
            (validHistory_pure _ _ _))
          (fun _ => validHistory_write_bind
            (by have := ht'.2; dsimp only [octWorkspace, keepBase] at *; omega) h1
            (validHistory_pure _ _ _))
      · exact clientResult_termInnerStep _ t'
    · exact clientResult_termOuterStep _ t
  refine validHistory_bind_ready hs3 (validHistory_minSepProg (d := (n, m)) hw hs3)
    fun _ t4 hs4 => ?_
  refine validHistory_bind_ready hs4 ?_ fun _ t5 hs5 => ?_
  · unfold countDelProg
    dsimp only
    refine validHistory_read_bind (by have := hs4.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_fst (Inv := MemReady w n) L 0 0 (fun j hj cnt t ht => ⟨?_, ?_⟩) hs4)
      (validHistory_pure _ _ _)
    · unfold countDelStep
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
      exact validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, digitBase] at *; omega)
        (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _))
    · exact (clientResult_countDelStep _ t).1
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_ready hs5 ?_ fun _ _ _ => validHistory_pure _ _ _
  unfold commitLeafProg
  refine validHistory_read_bind (by have := hs5.2; dsimp only [octWorkspace] at *; omega) ?_
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs5)
    (validHistory_pure _ _ _)
  · unfold commitStep
    dsimp only
    have hfr := ht.2
    have hsq := splitCount_sq n
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, wBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, guessBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, sepOutBase, parBase, distBase, flowBase,
        splitCount] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, colBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr hv ⊢; omega) ?_
    have hsaddr : sepBase n + v < t.frontier := by
      dsimp only [octWorkspace, sepBase] at hfr hv ⊢; omega
    have hw1 : ∀ val, Fits w val →
        (Memory.spec w).ValidHistory ⟨Function.update t.mem (sepBase n + v) val, t.frontier⟩
          ((Memory.spec w).clientHistory ⟨Function.update t.mem (sepBase n + v) val, t.frontier⟩
            (do
              if t.mem (wBase n + v) = 1 then
                if t.mem (guessBase n + v) = 2 then Memory.write (colBase n + v) 1
                else Memory.write (colBase n + v) 0
              else if t.mem (distBase n + (v + n + 2)) < splitCount n then
                if t.mem (colBase n + v) = 1 then Memory.write (colBase n + v) 1
                else Memory.write (colBase n + v) 0
              else if t.mem (colBase n + v) = 1 then Memory.write (colBase n + v) 0
              else Memory.write (colBase n + v) 1
              pure (v + 1))) := by
      intro val _
      have hcaddr : colBase n + v < t.frontier := by
        dsimp only [octWorkspace, colBase] at hfr hv ⊢; omega
      split_ifs <;>
        first
        | exact validHistory_write_bind hcaddr h1 (validHistory_pure _ _ _)
        | exact validHistory_write_bind hcaddr (fits_zero w) (validHistory_pure _ _ _)
    exact validHistory_ite
      (fun _ => validHistory_write_bind hsaddr h1 (hw1 1 h1))
      (fun _ => validHistory_write_bind hsaddr (fits_zero w) (hw1 0 (fits_zero w)))
  · exact clientResult_commitStep _ t

private theorem validHistory_compressProg {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1.1.1)) (hL : d.2 ≤ d.1.1.1) (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (compressProg d)) := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hw hL hs
  unfold compressProg
  dsimp only [CompressCfg.n]
  have hf := validHistory_fillRange (d := ((digitBase n, 0), L)) hs
    (by dsimp only [octWorkspace, digitBase]; omega) (fits_zero w)
  refine validHistory_bind_step hf ?_
  have hs1 := MonotoneMemInv.pres hs hf
  refine validHistory_bind_step
    (validHistory_boundedWhile_inv (MemReady w n) (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep
      (((n, k), m), L) (fun st t ht _ => ?_) (3 ^ L) (0, 0) hs1)
    (validHistory_pure _ _ _)
  have hodom : ∀ (found' : ℕ) (t1 : Memory.State), MemReady w n t1 →
      (Memory.spec w).ValidHistory t1
        ((Memory.spec w).clientHistory t1
          (incOdomProg (n, L) >>= fun done' => pure (done', found'))) := by
    intro found' t1 ht1
    refine validHistory_bind_step ?_ (validHistory_pure _ _ _)
    unfold incOdomProg
    dsimp only
    refine validHistory_read_bind (by have := ht1.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_fst (Inv := MemReady w n) L 0 1
        (fun j hj carry t' ht' => ⟨?_, ?_⟩) ht1)
      (validHistory_pure _ _ _)
    · unfold incOdomStep
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
      refine validHistory_read_bind
        (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      exact validHistory_ite
        (fun hlt => validHistory_write_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega)
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_write_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega)
          (fits_zero w) (validHistory_pure _ _ _))
    · exact clientResult_incOdomStep_fst _ t'
  dsimp only [guessStep, GuessStepArgs.n, GuessStepArgs.L, GuessStepArgs.found]
  refine validHistory_read_bind (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · have hlf := validHistory_leafProg (d := (((n, k), m), L)) hw hL ht
    exact validHistory_bind_step hlf (hodom _ _ (MonotoneMemInv.pres ht hlf))
  · exact validHistory_bind_step (validHistory_pure _ _ _) (hodom _ t ht)

/-- `encodeInput G k` satisfies `InputFits` when `Fits w (octWorkspace n)` and `Fits w k`. -/
theorem inputFits_encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k w : ℕ} (hw : Fits w (octWorkspace n)) (hk : Fits w k) :
    InputFits w (encodeInput G k) := by
  refine ⟨?_, ?_⟩
  · rw [length_encodeInput]
    apply hw.of_le
    dsimp only [octWorkspace]
    omega
  · intro u hu
    simp only [encodeInput, List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · apply hw.of_le; dsimp only [octWorkspace]; omega
    · exact hk
    · simp only [encodeAdjMatrix, List.mem_ofFn] at hu
      obtain ⟨idx, rfl⟩ := hu
      split_ifs
      · apply hw.of_le; dsimp only [octWorkspace]; omega
      · exact fits_zero w

private theorem init_mem_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (Memory.State.init (encodeInput G k)).mem 1 = n :=
  rfl

private theorem init_mem_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (Memory.State.init (encodeInput G k)).mem 2 = k :=
  rfl

private theorem init_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (Memory.State.init (encodeInput G k)).frontier = 3 + n * n := by
  change (encodeInput G k).length + 1 = 3 + n * n
  rw [length_encodeInput]
  omega

/-- Every step of `octProg ()` is history-valid under `Memory.spec w`. -/
theorem validHistory_octProg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k w : ℕ} (hw : Fits w (octWorkspace n)) (hk : Fits w k) :
    let s₀ := Memory.State.init (encodeInput G k)
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (octProg ())) := by
  intro s₀
  have hfr0 : s₀.frontier = 3 + n * n := init_frontier G k
  have hm1 : s₀.mem 1 = n := init_mem_one G k
  have hm2 : s₀.mem 2 = k := init_mem_two G k
  have hin : InputFits w (encodeInput G k) := inputFits_encodeInput G hw hk
  have hfit0 : Fits w ((encodeInput G k).length + 1) := by
    rw [length_encodeInput]
    apply hw.of_le
    dsimp only [octWorkspace]
    omega
  have hwf0 : Memory.WellFormed w s₀ := Memory.wellFormed_init hin hfit0
  unfold octProg
  refine validHistory_read_bind (by omega) ?_
  rw [hm1]
  refine validHistory_read_bind (by omega) ?_
  rw [hm2]
  have halloc : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.alloc (octScratch n))) :=
    validHistory_alloc (by rw [hfr0, frontier_add_octScratch]; exact hw)
  refine validHistory_bind_step halloc ?_
  have hs1 : MemReady w n ((Memory.spec 0).clientState s₀ (Memory.alloc (octScratch n))) := by
    refine ⟨wellFormed_clientState hwf0 halloc, ?_⟩
    change octWorkspace n ≤ s₀.frontier + octScratch n
    rw [hfr0, frontier_add_octScratch]
  have hf1 := validHistory_fillRange (d := ((sepBase n, 0), n)) hs1
    (by dsimp only [octWorkspace, sepBase]; omega) (fits_zero w)
  refine validHistory_bind_step hf1 ?_
  have hs2 := MonotoneMemInv.pres hs1 hf1
  have hf2 := validHistory_fillRange (d := ((colBase n, 0), n)) hs2
    (by dsimp only [octWorkspace, colBase]; omega) (fits_zero w)
  refine validHistory_bind_step hf2 ?_
  have hs3 := MonotoneMemInv.pres hs2 hf2
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := MemReady w n) n 0 1 (fun m hm alive t ht => ⟨?_, ?_⟩) hs3)
    (validHistory_pure _ _ _)
  · unfold octStep
    dsimp only [OctStepArgs.n, OctStepArgs.k, OctStepArgs.m, OctStepArgs.alive]
    refine validHistory_read_bind (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
    have hbw := validHistory_buildWProg (d := (n, m)) hw (by dsimp only; omega) ht
    refine validHistory_bind_step hbw ?_
    have ht1 := MonotoneMemInv.pres ht hbw
    refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
    · exact validHistory_write_bind
        (by have := ht1.2; dsimp only [octWorkspace, sepBase] at *; omega)
        (by apply hw.of_le; dsimp only [octWorkspace]; omega)
        (validHistory_pure _ _ _)
    · exact validHistory_ite
        (fun hLn => validHistory_bind_step
          (validHistory_compressProg (d := (((n, k), m + 1), _)) hw hLn ht1)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_pure _ _ _)
  · exact clientResult_octStep_fst _ t

end Cslib.Algorithms.WordRAM.OddCycleTransversal
