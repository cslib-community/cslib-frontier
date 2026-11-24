/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.CompressProg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Instruction-level `memoryCost` bounds for `octProg` subroutines

This module proves explicit polynomial / FPT `memoryCost` upper bounds for `readSplitCap`,
`readResCap`, `bfsProg`, `minSepProg`, `leafProg`, and `compressProg`. It builds in parallel with
`Validity`, `MinSep`, and `LeafSubroutines`.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.memoryCost_compressProg_le`: `O(3 ^ L · n ^ 4)`
  memory-cost bound for `compressProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write clientState_map

private theorem memoryCost_readSplitCap_le (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readSplitCap d) s ≤ 2 := by
  unfold readSplitCap
  have hbody : ∀ t, memoryCost
      (if d.1.2 = 0 then
        if 2 ≤ d.2 ∧ d.2 < d.1.1.1 + 2 then
          do let a ← Memory.read (keepBase d.1.1.1 + (d.2 - 2))
             if a = 1 then pure (d.1.1.1 + 1) else pure 0
        else pure 0
      else if d.2 = 1 then
        if d.1.1.1 + 2 ≤ d.1.2 ∧ d.1.2 < splitCount d.1.1.1 then
          do let b ← Memory.read (flipBase d.1.1.1 + (d.1.2 - (d.1.1.1 + 2)))
             if b = 1 then pure (d.1.1.1 + 1) else pure 0
        else pure 0
      else if 2 ≤ d.1.2 ∧ d.1.2 < d.1.1.1 + 2 then
        if d.2 = d.1.2 + d.1.1.1 then
          do let z ← Memory.read (wBase d.1.1.1 + (d.1.2 - 2))
             if z = 0 then pure 1 else pure 0
        else pure 0
      else if d.1.1.1 + 2 ≤ d.1.2 ∧ d.1.2 < splitCount d.1.1.1 ∧
          2 ≤ d.2 ∧ d.2 < d.1.1.1 + 2 then
        if d.1.2 - (d.1.1.1 + 2) < d.1.1.2 ∧ d.2 - 2 < d.1.1.2 then
          do let e ← Memory.read (3 + (d.1.2 - (d.1.1.1 + 2)) * d.1.1.1 + (d.2 - 2))
             if e = 1 then pure (d.1.1.1 + 1) else pure 0
        else pure 0
      else pure 0) t ≤ 1 := by
    intro t
    have hleaf : ∀ a c1 c2,
        memoryCost (do let e ← Memory.read a; if e = c1 then pure c2 else pure 0) t ≤ 1 := by
      intro a c1 c2
      exact le_trans (memoryCost_bind_le (memoryCost_read a t).le fun _ t' =>
        memoryCost_ite_le (memoryCost_pure _ t').le (memoryCost_pure 0 t').le) (by decide)
    refine memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) ?_
    refine memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) ?_
    refine memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) ?_
    exact memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) (Nat.zero_le _)
  exact le_trans (memoryCost_bind_le (memoryCost_read 0 s).le fun _ t => hbody t) (by decide)

private theorem memoryCost_readResCap_le (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readResCap d) s ≤ 4 := by
  unfold readResCap
  refine le_trans (memoryCost_bind_le (memoryCost_readSplitCap_le d s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_read _ t1).le fun _ t2 =>
      memoryCost_bind_le (memoryCost_read _ t2).le fun _ t3 =>
        memoryCost_ite_le (memoryCost_pure _ t3).le (memoryCost_pure 0 t3).le) (by decide)

private theorem memoryCost_bfsProg_le (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (bfsProg d) s ≤ 80 * (d.1 + 1) ^ 3 := by
  rcases d with ⟨n, m⟩
  dsimp only
  let M := splitCount n
  have hM : M = 2 * (n + 1) := by dsimp only [M, splitCount]; omega
  unfold bfsProg
  dsimp only
  have hlayer : ∀ l t, memoryCost (bfsLayerStep ((n, m), l)) t ≤ 9 * M * M := by
    intro l t
    unfold bfsLayerStep
    dsimp only
    have hmid : ∀ u t', memoryCost (bfsMidStep (((n, m), l), u)) t' ≤ 8 * M := by
      intro u t'
      unfold bfsMidStep
      dsimp only
      have hinn : ∀ v t4, memoryCost (bfsInnerStep ((((n, m), l), u), v)) t4 ≤ 7 := by
        intro v t4
        unfold bfsInnerStep
        dsimp only
        exact le_trans (memoryCost_bind_le (memoryCost_read _ t4).le fun _ t5 =>
          memoryCost_bind_le (memoryCost_readResCap_le (((n, m), u), v) t5) fun _ t6 =>
            memoryCost_ite_le
              (memoryCost_bind_le (memoryCost_write _ _ t6).le fun _ t7 =>
                (le_refl 1 : memoryCost _ t7 ≤ 1))
              (Nat.zero_le _))
          (by decide)
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t').le fun _ t3 =>
        memoryCost_ite_le (memoryCost_bind_le (memoryCost_iterate_le_of bfsInnerStep 7 (((n, m),
          l), u) hinn M 0 t3)
          fun _ t4 => (memoryCost_pure _ t4).le) (Nat.zero_le _)) (by omega)
    exact le_trans (memoryCost_bind_le (memoryCost_read 0 t).le fun _ t' =>
      memoryCost_bind_le (memoryCost_iterate_le_of bfsMidStep (8 * M) ((n, m), l) hmid M 0 t')
        fun _ t'' => (memoryCost_pure _ t'').le) (by nlinarith [hM])
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((distBase n, M), M) s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_write _ _ t1).le fun _ t2 =>
      memoryCost_bind_le (memoryCost_write _ _ t2).le fun _ t3 =>
        memoryCost_bind_le (memoryCost_iterate_le_of bfsLayerStep (9 * M * M) (n,
          m) hlayer (M - 1) 0 t3)
          fun _ t4 => (memoryCost_pure () t4).le) ?_
  dsimp only
  have hsub : M - 1 ≤ M := Nat.sub_le _ _
  have hmul : 9 * M * M * (M - 1) ≤ 9 * M * M * M := Nat.mul_le_mul_left _ hsub
  have hM3 : 9 * M * M * M = 72 * (n + 1) ^ 3 := by rw [hM]; ring
  have hp1 : n + 1 ≤ (n + 1) ^ 3 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 3)
  omega

private theorem memoryCost_minSepProg_le (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minSepProg d) s ≤ 180 * (d.1 + 1) ^ 4 := by
  rcases d with ⟨n, m⟩
  dsimp only
  let M := splitCount n
  have hM : M = 2 * (n + 1) := by dsimp only [M, splitCount]; omega
  have hp1 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hp2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 2 ≤ 4)
  have hp3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 3 ≤ 4)
  have hn3 : n * ((n + 1) ^ 3) ≤ (n + 1) ^ 4 := by
    calc n * (n + 1) ^ 3 ≤ (n + 1) * (n + 1) ^ 3 := Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = (n + 1) ^ 4 := by ring
  unfold minSepProg
  dsimp only
  have hpush : ∀ cur t3, memoryCost (pushUnitStep (n, cur)) t3 ≤ 5 := by
    intro cur t3
    unfold pushUnitStep
    dsimp only
    exact le_trans (memoryCost_bind_le (memoryCost_read 0 t3).le fun _ t4 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ t4).le fun _ t5 =>
        memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ t5).le fun _ t6 =>
          memoryCost_ite_le (k := 2) (le_trans (le_refl 1 : memoryCost _ t6 ≤ 1) (by decide))
            (memoryCost_bind_le (k₂ := 1) (memoryCost_read _ t6).le fun _ t7 =>
              memoryCost_ite_le (k := 1) (le_refl 1) (Nat.zero_le _)))
          (Nat.zero_le _))
        (Nat.zero_le _)) (by decide)
  have haug : ∀ r t, memoryCost (augRoundStep ((n, m), r)) t ≤ 91 * (n + 1) ^ 3 := by
    intro r t
    unfold augRoundStep
    dsimp only
    have hpow : n + 1 ≤ (n + 1) ^ 3 := by
      simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 3)
    have hbranch : ∀ d1 t'',
        memoryCost (if d1 < splitCount n then do let _ ← iterate pushUnitStep n d1 1; pure (r + 1)
          else pure (r + 1)) t'' ≤ 5 * M := by
      intro d1 t''
      rw [memoryCost_ite]
      split_ifs with hd1
      · refine le_trans (memoryCost_bind_le (memoryCost_iterate_le_of pushUnitStep 5 n hpush d1 1
        t'')
          fun _ t3 => (memoryCost_pure _ t3).le) ?_
        have : 5 * d1 ≤ 5 * M := Nat.mul_le_mul_left 5 (le_of_lt hd1)
        omega
      · exact Nat.zero_le _
    refine le_trans (memoryCost_bind_le (memoryCost_bfsProg_le (n, m) t) fun _ t' =>
      memoryCost_bind_le (memoryCost_read _ t').le fun d1 t'' => hbranch d1 t'') ?_
    dsimp only
    omega
  have hext : ∀ vc t4, memoryCost (extractSepStep (n, vc)) t4 ≤ 4 := by
    intro vc t4
    unfold extractSepStep
    exact le_trans (memoryCost_bind_le (memoryCost_read _ t4).le fun _ t5 =>
      memoryCost_bind_le (memoryCost_read _ t5).le fun _ t6 =>
        memoryCost_bind_le (memoryCost_read _ t6).le fun _ t7 =>
          memoryCost_ite_le ((le_refl 1)) ((le_refl 1))) (by decide)
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((flowBase n, 0),
    M * M) s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_iterate_le_of augRoundStep (91 * (n + 1) ^ 3) (n, m) haug n 0 t1)
      fun _ t2 =>
        memoryCost_bind_le (memoryCost_bfsProg_le (n, m) t2) fun _ t3 =>
          memoryCost_bind_le (memoryCost_iterate_le_of extractSepStep 4 n hext n (0, 0) t3)
            fun _ t4 => (memoryCost_pure _ t4).le) ?_
  dsimp only
  have hMM : M * M = 4 * (n + 1) ^ 2 := by rw [hM]; ring
  have h91 : 91 * (n + 1) ^ 3 * n = 91 * (n * (n + 1) ^ 3) := by ring
  omega

private theorem memoryCost_leafProg_le {d : ((ℕ × ℕ) × ℕ) × ℕ} (hL : d.2 ≤ d.1.1.1)
    (s : Memory.State) :
    memoryCost (leafProg d) s ≤ 210 * (d.1.1.1 + 1) ^ 4 := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hL ⊢
  have hp1 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hp2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 2 ≤ 4)
  have hunp : ∀ t, memoryCost (unpackGuessProg (n, L)) t ≤ 4 * (n + 1) := by
    intro t
    unfold unpackGuessProg
    dsimp only
    have hstep : ∀ j t2, memoryCost (unpackStep (n, j)) t2 ≤ 3 := fun j t2 => by
      unfold unpackStep
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t2).le fun _ t3 =>
        memoryCost_bind_le (memoryCost_read _ t3).le fun _ t4 =>
          memoryCost_ite_le ((le_refl 1)) (Nat.zero_le _)) (by decide)
    exact le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((guessBase n, 0), n) t) fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of unpackStep 3 n hstep L 0 t1)
        fun _ t2 => (memoryCost_pure () t2).le)
      (by dsimp only; omega)
  have hchk : ∀ t, memoryCost (checkProperProg ((n, m), L)) t ≤ 6 * (n + 1) ^ 2 := by
    intro t
    unfold checkProperProg
    have hout : ∀ iok t3, memoryCost (properOuterStep (((n, m), L), iok)) t3 ≤ 3 * L + 2 := by
      intro iok t3
      unfold properOuterStep
      have hinn : ∀ (u du : ℕ) jok t5,
          memoryCost (properInnerStep ((((n, m), u), du), jok)) t5 ≤ 3 := fun u du jok t5 => by
        unfold properInnerStep
        exact le_trans (memoryCost_bind_le (memoryCost_read _ t5).le fun _ t6 =>
          memoryCost_bind_le (memoryCost_read _ t6).le fun _ t7 =>
            memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ t7).le fun _ t8 =>
              memoryCost_ite_le (memoryCost_pure _ t8).le (memoryCost_pure _ t8).le)
              (Nat.zero_le _)) (by decide)
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t3).le fun u t4 =>
        memoryCost_bind_le (memoryCost_read _ t4).le fun du t5 =>
          memoryCost_ite_le (memoryCost_bind_le (memoryCost_iterate_le_of properInnerStep 3 (((n,
            m), u), du)
            (hinn u du) L (0, iok.2) t5) fun _ t6 => (memoryCost_pure _ t6).le)
            (Nat.zero_le _)) (by omega)
    exact le_trans (memoryCost_bind_le (memoryCost_read 0 t).le fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of properOuterStep (3 * L + 2) ((n, m),
        L) hout L (0, 1) t2)
        fun _ t3 => (memoryCost_pure _ t3).le) (by nlinarith [hL])
  have hterm : ∀ t, memoryCost (buildTerminalsProg ((n, m), L)) t ≤ 8 * (n + 1) ^ 2 := by
    intro t
    unfold buildTerminalsProg
    dsimp only
    have hout : ∀ v t5, memoryCost (termOuterStep (((n, m), L), v)) t5 ≤ 4 * L + 2 := by
      intro v t5
      unfold termOuterStep
      have hinn : ∀ (cv : ℕ) j t7,
          memoryCost (termInnerStep (((n, m), (v, cv)), j)) t7 ≤ 4 := fun cv j t7 => by
        unfold termInnerStep
        exact le_trans (memoryCost_bind_le (memoryCost_read _ t7).le fun _ t8 =>
          memoryCost_bind_le (memoryCost_read _ t8).le fun _ t9 =>
            memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ t9).le fun _ t10 =>
              memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
                (Nat.zero_le _)) (Nat.zero_le _)) (by decide)
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t5).le fun _ t6 =>
        memoryCost_bind_le (memoryCost_read _ t6).le fun cv t7 =>
          memoryCost_ite_le (memoryCost_bind_le (memoryCost_iterate_le_of termInnerStep 4 ((n, m),
            (v, cv))
            (hinn cv) L 0 t7) fun _ t8 => (memoryCost_pure _ t8).le) (Nat.zero_le _)) (by omega)
    exact le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((keepBase n, 0), n) t) fun _ t1 =>
      memoryCost_bind_le (memoryCost_fillRange_le ((flipBase n, 0), n) t1) fun _ t2 =>
        memoryCost_bind_le (memoryCost_iterate_le_of termOuterStep (4 * L + 2) ((n, m),
          L) hout n 0 t2)
          fun _ t3 => (memoryCost_pure () t3).le) (by dsimp only; nlinarith [hL])
  have hcdel : ∀ t, memoryCost (countDelProg (n, L)) t ≤ 2 * (n + 1) := by
    intro t
    unfold countDelProg
    have hstep : ∀ jc t2, memoryCost (countDelStep (n, jc)) t2 ≤ 1 := fun jc t2 => by
      unfold countDelStep
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t2).le fun _ t3 =>
        memoryCost_ite_le (memoryCost_pure _ t3).le (memoryCost_pure _ t3).le) (by decide)
    exact le_trans (memoryCost_bind_le (memoryCost_read 0 t).le fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of countDelStep 1 n hstep L (0, 0) t1)
        fun _ t2 => (memoryCost_pure _ t2).le) (by omega)
  have hcom : ∀ t, memoryCost (commitLeafProg n) t ≤ 8 * (n + 1) := by
    intro t
    unfold commitLeafProg
    have hstep : ∀ v t2, memoryCost (commitStep (n, v)) t2 ≤ 7 := fun v t2 => by
      unfold commitStep
      have hcol : ∀ t7 : Memory.State, ∀ c1 c2 c3 c4 c5 : Prop,
          [Decidable c1] → [Decidable c2] → [Decidable c3] → [Decidable c4] → [Decidable c5] →
          memoryCost
            (if c1 then
              if c2 then (fun _ => v + 1) <$> Memory.write (colBase n + v) 1
              else (fun _ => v + 1) <$> Memory.write (colBase n + v) 0
            else if c3 then
              if c4 then (fun _ => v + 1) <$> Memory.write (colBase n + v) 1
              else (fun _ => v + 1) <$> Memory.write (colBase n + v) 0
            else if c5 then (fun _ => v + 1) <$> Memory.write (colBase n + v) 0
            else (fun _ => v + 1) <$> Memory.write (colBase n + v) 1) t7 ≤ 1 := by
        intro t7 c1 c2 c3 c4 c5 _ _ _ _ _
        exact memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
          (memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
            (memoryCost_ite_le ((le_refl 1)) ((le_refl 1))))
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t2).le fun _ t3 =>
        memoryCost_bind_le (memoryCost_read _ t3).le fun _ t4 =>
          memoryCost_bind_le (memoryCost_read _ t4).le fun _ t5 =>
            memoryCost_bind_le (memoryCost_read _ t5).le fun _ t6 =>
              memoryCost_bind_le (memoryCost_read _ t6).le fun _ t7 =>
                memoryCost_ite_le
                  (memoryCost_bind_le (memoryCost_write _ _ t7).le fun _ t8 =>
                    hcol t8 _ _ _ _ _)
                  (memoryCost_bind_le (memoryCost_write _ _ t7).le fun _ t8 =>
                    hcol t8 _ _ _ _ _)) (by decide)
    exact le_trans (memoryCost_bind_le (memoryCost_read 0 t).le fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of commitStep 7 n hstep n 0 t1)
        fun _ t2 => (memoryCost_pure () t2).le) (by omega)
  unfold leafProg
  dsimp only
  refine le_trans (memoryCost_bind_le (hunp s) fun _ t1 =>
    memoryCost_bind_le (hchk t1) fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (hterm t2) fun _ t3 =>
        memoryCost_bind_le (memoryCost_minSepProg_le (n, m) t3) fun _ t4 =>
          memoryCost_bind_le (hcdel t4) fun _ t5 =>
            memoryCost_ite_le
              (memoryCost_bind_le (hcom t5) fun _ t6 => (memoryCost_pure 1 t6).le)
              (Nat.zero_le _))
        (Nat.zero_le _)) ?_
  dsimp only
  omega

/-- Upper bound on the instruction-level memory cost of `compressProg`. -/
theorem memoryCost_compressProg_le {d : ((ℕ × ℕ) × ℕ) × ℕ}
    (hL : d.2 ≤ CompressCfg.n d)
    (s : Memory.State) :
    memoryCost (compressProg d) s ≤ 215 * 3 ^ d.2 * (CompressCfg.n d + 1) ^ 4 := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only [CompressCfg.n] at hL ⊢
  have hp1 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hpow : 1 ≤ 3 ^ L := Nat.one_le_pow L 3 (by decide)
  have hodom : ∀ t', memoryCost (incOdomProg (n, L)) t' ≤ 3 * (n + 1) := by
    intro t'
    unfold incOdomProg
    have hstep : ∀ jc t2, memoryCost (incOdomStep (n, jc)) t2 ≤ 2 := fun jc t2 => by
      unfold incOdomStep
      exact le_trans (memoryCost_bind_le (memoryCost_read _ t2).le fun _ t3 =>
        memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
          (Nat.zero_le _))
        (by decide)
    exact le_trans (memoryCost_bind_le (memoryCost_read 0 t').le fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of incOdomStep 2 n hstep L (0, 1) t1)
        fun _ t2 => (memoryCost_pure _ t2).le) (by omega)
  have hguess : ∀ st t, st.1 = 0 →
      memoryCost (guessStep ((((n, k), m), L), st)) t ≤ 214 * (n + 1) ^ 4 := by
    intro st t _
    dsimp only [guessStep]
    refine le_trans (memoryCost_bind_le (memoryCost_read 0 t).le fun _ t2 =>
      memoryCost_ite_le
        (memoryCost_bind_le (memoryCost_leafProg_le (d := (((n, k), m), L)) hL t2) fun _ t3 =>
          memoryCost_bind_le (hodom t3) fun _ t4 => (memoryCost_pure _ t4).le)
        (le_trans (memoryCost_bind_le (memoryCost_pure st.2 t2).le fun _ t3 =>
          memoryCost_bind_le (hodom t3) fun _ t4 => (memoryCost_pure _ t4).le)
          (by dsimp only; omega))) ?_
    dsimp only
    omega
  unfold compressProg
  dsimp only
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((digitBase n, 0), L) s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_boundedWhile_le_of (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep
      (214 * (n + 1) ^ 4) (((n, k), m), L) hguess (3 ^ L) (0, 0) t1)
      fun _ t2 => (memoryCost_pure _ t2).le) ?_
  dsimp only
  nlinarith [hL]

end Cslib.Algorithms.WordRAM.OddCycleTransversal
