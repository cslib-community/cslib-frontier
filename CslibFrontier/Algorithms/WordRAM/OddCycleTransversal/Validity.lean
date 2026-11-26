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

attribute [local client_simps] runClient_read runClient_write StateTransitionSpec.clientState_map

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

private theorem flowAddr_lt_frontier {w n a b : ℕ} {s : Memory.State}
    (hs : MemReady w n s) (ha : a < splitCount n) (hb : b < splitCount n) :
    flowBase n + a * splitCount n + b < s.frontier := by
  have hfr := hs.2
  have hsq := splitCount_sq n
  have hlt : a * splitCount n + b < splitCount n * splitCount n := by nlinarith
  dsimp only [octWorkspace, flowBase, splitCount] at hfr hlt ⊢
  omega

private theorem validHistory_readResCap {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w d.1.1.1 s) (hx : d.1.2 < splitCount d.1.1.1) (hy : d.2 < splitCount d.1.1.1) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readResCap d)) := by
  rcases d with ⟨⟨⟨n, m⟩, x⟩, y⟩
  dsimp only at hs hx hy
  unfold readResCap
  refine validHistory_bind_step (validHistory_readSplitCap hs) ?_
  rw [clientState_readSplitCap]
  exact validHistory_read_bind (flowAddr_lt_frontier hs hx hy)
    (validHistory_read_bind (flowAddr_lt_frontier hs hy hx)
      (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)))

private theorem validHistory_bfsProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bfsProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hs
  have hsq := splitCount_sq n
  unfold bfsProg
  dsimp only
  refine validHistory_bind_ready hs
    (validHistory_fillRange hs
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount]; omega)
      (hw.of_le (by dsimp only [octWorkspace, splitCount]; omega)))
    fun _ s1 hs1 => ?_
  have hfr1 := hs1.2
  have hd0 : distBase n < s1.frontier := by
    dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr1 ⊢; omega
  have hp0 : parBase n < s1.frontier := by
    dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hfr1 ⊢; omega
  refine validHistory_write_bind hd0 (fits_zero w) (validHistory_write_bind hp0 (fits_zero w) ?_)
  have hs2 := memReady_write (memReady_write hs1 (distBase n) 0 (fits_zero w))
    (parBase n) 0 (fits_zero w)
  have hdist_lt {v : ℕ} (hv : v < 0 + splitCount n) {t : Memory.State} (ht : MemReady w n t) :
      distBase n + v < t.frontier := by
    have := ht.2
    dsimp only [octWorkspace, distBase, flowBase, splitCount] at hv this ⊢; omega
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
      refine validHistory_read_bind (hdist_lt hu ht') ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n) 0
          (fun v hv t'' ht'' => ⟨?_, ?_⟩) ht')
        (validHistory_pure _ _ _)
      · unfold bfsInnerStep
        dsimp only [BfsInnerArgs.n, BfsInnerArgs.m, BfsInnerArgs.layer, BfsInnerArgs.u]
        refine validHistory_read_bind (hdist_lt hv ht'') ?_
        refine validHistory_bind_ready ht''
          (validHistory_readResCap (d := (((n, m), u), v)) ht''
            (hu.trans_eq (Nat.zero_add _)) (hv.trans_eq (Nat.zero_add _)))
          fun _ t3 ht3 => validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_write_bind (hdist_lt hv ht3)
          (hw.of_le (by dsimp only [octWorkspace, splitCount] at hlayer ⊢; omega)) ?_
        exact validHistory_write_bind
          (by have := ht3.2
              dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hv this ⊢
              omega)
          (hw.of_le (by dsimp only [octWorkspace, splitCount] at hu ⊢; omega))
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
  refine validHistory_bind_ready hs
    (validHistory_fillRange hs
      (by dsimp only [octWorkspace, flowBase, splitCount]; omega) (fits_zero w))
    fun _ s1 hs1 => ?_
  refine validHistory_bind_ready hs1
    (validHistory_iterate_inv (MemReady w n) augRoundStep (n, m)
      (fun r t ht => by
        unfold augRoundStep
        dsimp only [GraphStepArgs.n, GraphStepArgs.m]
        refine validHistory_bind_ready ht (validHistory_bfsProg (d := (n, m)) hw ht)
          fun _ t1 ht1 => ?_
        refine validHistory_read_bind
          (by have := ht1.2
              dsimp only [octWorkspace, distBase, flowBase, splitCount] at *; omega) ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_bind_step
          (validHistory_iterate_inv (MemReady w n) pushUnitStep n (fun cur t' ht' => ?_) _ 1 ht1)
          (validHistory_pure _ _ _)
        unfold pushUnitStep
        dsimp only
        have hfr' := ht'.2
        refine validHistory_read_bind (by dsimp only [octWorkspace] at hfr' ⊢; omega) ?_
        refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_read_bind
          (by dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hcur hfr' ⊢
              omega) ?_
        refine validHistory_ite (fun hu => ?_) (fun _ => validHistory_pure _ _ _)
        have had1 := flowAddr_lt_frontier ht' hcur hu
        have had2 := flowAddr_lt_frontier ht' hu hcur
        refine validHistory_read_bind had1 ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
        · exact validHistory_write_bind had1 ((ht'.1.mem_fits _).of_le (Nat.sub_le _ _))
            (validHistory_pure _ _ _)
        · refine validHistory_read_bind had2 ?_
          refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
          exact validHistory_write_bind had2 (hw.of_le (by dsimp only [octWorkspace]; omega))
            (validHistory_pure _ _ _))
      n 0 hs1)
    fun _ s2 hs2 => ?_
  refine validHistory_bind_ready hs2 (validHistory_bfsProg (d := (n, m)) hw hs2)
    fun _ s3 hs3 => ?_
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
      (fun _ => validHistory_write_bind hsep (hw.of_le (by dsimp only [octWorkspace]; omega))
        (validHistory_pure _ _ _))
      (fun _ => validHistory_write_bind hsep (fits_zero w) (validHistory_pure _ _ _))
  · exact (clientResult_extractSepStep _ t).1

private theorem validHistory_buildWProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hm : d.2 < d.1) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (buildWProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hm hs
  unfold buildWProg
  dsimp only
  refine validHistory_bind_ready hs
    (validHistory_copyRange hs
      (by dsimp only [octWorkspace, sepBase]; omega)
      (by dsimp only [octWorkspace, wBase]; omega))
    fun _ s1 hs1 => ?_
  have hwm : wBase n + m < s1.frontier := by
    have := hs1.2; dsimp only [octWorkspace, wBase] at *; omega
  have h1 : Fits w 1 := by apply hw.of_le; dsimp only [octWorkspace]; omega
  refine validHistory_write_bind hwm h1 ?_
  have hs2 := memReady_write hs1 (wBase n + m) 1 h1
  have hloop (rem : ℕ) : ∀ vL t, vL.1 + rem = n → vL.2 ≤ vL.1 → MemReady w n t →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate buildWListStep n rem vL)) := by
    induction rem with
    | zero => exact fun _ _ _ _ _ => validHistory_pure _ _ _
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
      obtain ⟨h1, h2⟩ := clientResult_buildWListStep (n, vL) t
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at h1 h2
      exact ih _ _ (by omega) (by omega) (MonotoneMemInv.pres ht hvstep)
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
    refine validHistory_bind_ready hs2
      (validHistory_fillRange hs2 (by dsimp only [octWorkspace, keepBase]; omega) (fits_zero w))
      fun _ _ hs2a => ?_
    refine validHistory_bind_ready hs2a
      (validHistory_fillRange hs2a (by dsimp only [octWorkspace, flipBase]; omega) (fits_zero w))
      fun _ _ hs2b => ?_
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
    have hcaddr : colBase n + v < t.frontier := by
      dsimp only [octWorkspace, colBase] at hfr hv ⊢; omega
    split_ifs <;>
      exact validHistory_write_bind hsaddr (by first | exact h1 | exact fits_zero w)
        (validHistory_write_bind hcaddr (by first | exact h1 | exact fits_zero w)
          (validHistory_pure _ _ _))
  · exact clientResult_commitStep _ t

private theorem validHistory_compressProg {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1.1.1)) (hL : d.2 ≤ d.1.1.1) (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (compressProg d)) := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hw hL hs
  unfold compressProg
  dsimp only [CompressCfg.n]
  refine validHistory_bind_ready hs
    (validHistory_fillRange hs (by dsimp only [octWorkspace, digitBase]; omega) (fits_zero w))
    fun _ _ hs1 => ?_
  refine validHistory_bind_step
    (validHistory_boundedWhile_inv (MemReady w n) (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep
      (((n, k), m), L) (fun st t ht _ => ?_) (3 ^ L) (0, 0) hs1)
    (validHistory_pure _ _ _)
  have hodom (found' : ℕ) (t1 : Memory.State) (ht1 : MemReady w n t1) :
      (Memory.spec w).ValidHistory t1
        ((Memory.spec w).clientHistory t1
          (incOdomProg (n, L) >>= fun done' => pure (done', found'))) := by
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
      have hfr' := ht'.2
      have hd : digitBase n + j < t'.frontier := by
        dsimp only [octWorkspace, digitBase] at hfr' hj ⊢; omega
      refine validHistory_read_bind hd ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      exact validHistory_ite
        (fun hlt => validHistory_write_bind hd
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_write_bind hd (fits_zero w) (validHistory_pure _ _ _))
    · exact clientResult_incOdomStep_fst _ t'
  dsimp only [guessStep, GuessStepArgs.n, GuessStepArgs.L, GuessStepArgs.found]
  refine validHistory_read_bind (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_bind_ready ht (validHistory_leafProg (d := (((n, k), m), L)) hw hL ht)
      fun _ => hodom _
  · exact validHistory_bind_step (validHistory_pure _ _ _) (hodom _ t ht)

/-- `encodeInput G k` satisfies `InputFits` when `Fits w (octWorkspace n)` and `Fits w k`. -/
theorem inputFits_encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k w : ℕ} (hw : Fits w (octWorkspace n)) (hk : Fits w k) :
    InputFits w (encodeInput G k) := by
  refine ⟨hw.of_le (by simp only [length_encodeInput, octWorkspace]; omega), fun u hu => ?_⟩
  simp only [encodeInput, List.mem_cons, encodeAdjMatrix, List.mem_ofFn] at hu
  rcases hu with rfl | rfl | ⟨_, rfl⟩
  · exact hw.of_le (by dsimp only [octWorkspace]; omega)
  · exact hk
  · split_ifs
    exacts [hw.of_le (by dsimp only [octWorkspace]; omega), fits_zero w]

/-- Every step of `octProg ()` is history-valid under `Memory.spec w`. -/
theorem validHistory_octProg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k w : ℕ} (hw : Fits w (octWorkspace n)) (hk : Fits w k) :
    let s₀ := Memory.State.init (encodeInput G k)
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (octProg ())) := by
  intro s₀
  have hfr0 : s₀.frontier = 3 + n * n := by
    simp only [s₀, Memory.State.init, length_encodeInput]; omega
  have hwf0 : Memory.WellFormed w s₀ :=
    Memory.wellFormed_init (inputFits_encodeInput G hw hk)
      (hw.of_le (by simp only [length_encodeInput, octWorkspace]; omega))
  unfold octProg
  refine validHistory_read_bind (by omega) ?_
  rw [show s₀.mem 1 = n from rfl]
  refine validHistory_read_bind (by omega) ?_
  rw [show s₀.mem 2 = k from rfl]
  have halloc : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.alloc (octScratch n))) :=
    validHistory_alloc (by rw [hfr0, frontier_add_octScratch]; exact hw)
  refine validHistory_bind_step halloc ?_
  have hs1 : MemReady w n ((Memory.spec 0).clientState s₀ (Memory.alloc (octScratch n))) :=
    ⟨wellFormed_clientState hwf0 halloc,
      ((congrArg (· + octScratch n) hfr0).trans (frontier_add_octScratch n)).ge⟩
  refine validHistory_bind_ready hs1
    (validHistory_fillRange hs1 (by dsimp only [octWorkspace, sepBase]; omega) (fits_zero w))
    fun _ _ hs2 => ?_
  refine validHistory_bind_ready hs2
    (validHistory_fillRange hs2 (by dsimp only [octWorkspace, colBase]; omega) (fits_zero w))
    fun _ _ hs3 => ?_
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
        (hw.of_le (by dsimp only [octWorkspace]; omega)) (validHistory_pure _ _ _)
    · exact validHistory_ite
        (fun hLn => validHistory_bind_step
          (validHistory_compressProg (d := (((n, k), m + 1), _)) hw hLn ht1)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_pure _ _ _)
  · exact clientResult_octStep_fst _ t

end Cslib.Algorithms.WordRAM.OddCycleTransversal
