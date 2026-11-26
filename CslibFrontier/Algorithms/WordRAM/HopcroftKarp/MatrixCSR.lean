/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Layout
import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Internal
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith

/-!
# Dense and square `0/1`-matrix to CSR conversion for word-RAM Hopcroft–Karp

Converts a row-major `m × r` `0/1` adjacency matrix in word-RAM memory into exact compressed sparse
row (CSR) neighbour arrays (`exactBipAdj`) and initializes the `BaseRegs` workspace pointers in
`O(m + m r)` instructions. Shared by dense Hopcroft–Karp
(`CslibFrontier.Algorithms.WordRAM.HopcroftKarp`) and Dilworth minimum chain cover / maximum
antichain (`CslibFrontier.Algorithms.WordRAM.ChainCover`).

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.buildCSRCode`: scans a row-major `m × r` `0/1` matrix at
  `matBase` into CSR arrays at `bOffReg` and sets up `BaseRegs`.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.matrixSetupCode`: reads header dimensions (`[m, r]` or
  square `[n]`), sets `bOffReg`, and runs `buildCSRCode`.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.exec_buildCSRCode`: `O(m + m r)` matrix-to-CSR conversion.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.exec_matrixSetupCode`: shared dense and square poset setup.
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg
open Cslib.Algorithms.WordRAM.HopcroftKarp.Internal

private def buildCSRColBody : Code .standard 34 := ram[
  val ← *qTail;
  qTail ← qTail + one;
  if val = one then [
    addr ← bEdgesReg + rE; *addr ← idx;
    rE ← rE + one
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def buildCSRRowBody : Code .standard 34 :=
  .seq (ram[ addr ← bOffReg + qHead; *addr ← rE; idx ← #0 ])
    (.seq (.loop (.lt idx rr) buildCSRColBody)
      (ram[ qHead ← qHead + one ]))

/-- Convert a row-major `m × r` `0/1` adjacency matrix stored starting at `matBase` into exact
CSR arrays starting at `bOffReg`, then initialize all `BaseRegs` workspace pointers. -/
def buildCSRCode (matBase : ℕ) : Code .standard 34 :=
  .seq (ram[ bEdgesReg ← bOffReg + rm; bEdgesReg ← bEdgesReg + one;
             rE ← #0; qHead ← #0; qTail ← #matBase ])
    (.seq (.loop (.lt qHead rm) buildCSRRowBody)
      (.seq (ram[ addr ← bOffReg + rm; *addr ← rE ])
        initBaseRegsFromCSR))

/-- Exact `O(m + m r)` matrix-to-CSR conversion and `BaseRegs` setup (`buildCSRCode`). -/
theorem exec_buildCSRCode {w m r matBase bOff : ℕ} (G : Fin m × Fin r → Bool) (x : Data 34)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (hrm : x.regs rm = m) (hrr : x.regs rr = r) (hbOff : x.regs bOffReg = bOff)
    (hmat_le : matBase + m * r ≤ bOff)
    (hmat : ∀ (u : Fin m) (v : Fin r),
      x.mem (matBase + (u.val * r + v.val)) = if G (u, v) then 1 else 0)
    (hfit : Fits w (bOff + 7 * m + 5 * r + m * r + 8)) :
    let sInst : SparseInstance := ⟨m, r, exactBipAdj G⟩
    ∃ z, ExecWithin w (buildCSRCode matBase) x z (9 * m * r + 8 * m + 25) ∧
      BaseRegs sInst bOff z ∧
      CSRMem sInst bOff z.mem := by
  let sInst : SparseInstance := ⟨m, r, exactBipAdj G⟩
  have hE_le : sInst.numEdges ≤ m * r := bipAdjSteps_exactBipAdj_le G
  let s₀ := ((((x.set bEdgesReg (bOff + m)).set bEdgesReg (bOff + m + 1)).set rE 0).set
    qHead 0).set qTail matBase
  have he₀ : ExecWithin w
      (.seq (ram[ bEdgesReg ← bOffReg + rm ]) (.seq (ram[ bEdgesReg ← bEdgesReg + one ])
        (.seq (ram[ rE ← #0 ]) (.seq (ram[ qHead ← #0 ]) (ram[ qTail ← #matBase ])))) :
        Code .standard 34) x s₀ 5 := by
    refine WP.execWithin ?_
    wram_exec [hbOff, hrm, h1]
    rfl
  let PR (uIdx : ℕ) (y : Data 34) : Prop :=
    uIdx ≤ m ∧
      (∀ i : Fin 34, i.val < 22 → i ≠ rE → y.regs i = s₀.regs i) ∧
      y.regs qTail = matBase + uIdx * r ∧
      y.regs rE = sInst.offset uIdx ∧
      (∀ u' : ℕ, u' < uIdx → y.mem (bOff + u') = sInst.offset u') ∧
      (∀ (u' : Fin m), u'.val < uIdx → ∀ {i : ℕ} (hi : i < (sInst.adj u').length),
        y.mem (bOff + m + 1 + (sInst.offset u'.val + i)) = ((sInst.adj u')[i]'hi).val) ∧
      (∀ a, a < bOff → y.mem a = x.mem a)
  have hPR₀ : PR 0 s₀ :=
    ⟨Nat.zero_le _, fun _ _ _ => rfl, by dsimp only [s₀]; wram_simp; omega,
      by dsimp only [s₀]; wram_simp [sInst.offset_zero],
      fun _ hu => absurd hu (Nat.not_lt_zero _),
      fun _ hu => absurd hu (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  have hrowBody (y : Data 34) (hy : PR (y.regs qHead) y) (hu_lt : y.regs qHead < m) :
      ∃ z, ExecWithin w buildCSRRowBody y z (9 * r + 6) ∧ PR (y.regs qHead + 1) z ∧
        z.regs qHead = y.regs qHead + 1 := by
    obtain ⟨_, hr_y, hqt_y, hrE_y, hoff_y, hedge_y, hlow_y⟩ := hy
    let u : Fin m := ⟨y.regs qHead, hu_lt⟩
    have hoff_succ : sInst.offset (u.val + 1) = sInst.offset u.val + (sInst.adj u).length :=
      sInst.offset_succ hu_lt
    have hoff_u1_le : sInst.offset (u.val + 1) ≤ m * r :=
      (sInst.offset_le_numEdges (u.val + 1)).trans hE_le
    have hy_bOff : y.regs bOffReg = bOff := by
      wram_simp [hr_y bOffReg (by decide) (by decide), s₀, hbOff]
    have hy_bEdges : y.regs bEdgesReg = bOff + m + 1 := by
      wram_simp [hr_y bEdgesReg (by decide) (by decide), s₀]
    have hy_zero : y.regs zero = 0 := by
      wram_simp [hr_y zero (by decide) (by decide), s₀, h0]
    have hy_one : y.regs one = 1 := by
      wram_simp [hr_y one (by decide) (by decide), s₀, h1]
    have hy_rr : y.regs rr = r := by
      wram_simp [hr_y rr (by decide) (by decide), s₀, hrr]
    let y₁ := ((y.set addr (bOff + y.regs qHead)).write
      (bOff + y.regs qHead) (sInst.offset u.val)).set idx 0
    have he_pre_row : ExecWithin w
        (.seq (ram[ addr ← bOffReg + qHead ])
          (.seq (ram[ *addr ← rE ]) (ram[ idx ← #0 ])) : Code .standard 34) y y₁ 3 := by
      refine WP.execWithin ?_
      wram_exec [hy_bOff, hrE_y]
      rfl
    let rowPre (t : ℕ) : List (Fin r) := ((List.finRange r).take t).filter fun v => G (u, v)
    have hrowPre_sub (t : ℕ) : (rowPre t).length ≤ (sInst.adj u).length :=
      (List.Sublist.filter _ (List.take_sublist t (List.finRange r))).length_le
    let PC (t : ℕ) (w_st : Data 34) : Prop :=
      t ≤ r ∧
        (∀ i : Fin 34, i.val < 28 → i ≠ rE → i ≠ qTail → w_st.regs i = y₁.regs i) ∧
        w_st.regs qTail = matBase + u.val * r + t ∧
        w_st.regs rE = sInst.offset u.val + (rowPre t).length ∧
        (∀ i : ℕ, (hi : i < (rowPre t).length) →
          w_st.mem (bOff + m + 1 + (sInst.offset u.val + i)) = ((rowPre t)[i]'hi).val) ∧
        (∀ a, ¬(bOff + m + 1 + sInst.offset u.val ≤ a ∧
            a < bOff + m + 1 + sInst.offset (u.val + 1)) → w_st.mem a = y₁.mem a)
    have hPC₀ : PC 0 y₁ :=
      ⟨Nat.zero_le _, fun _ _ _ _ => rfl,
        by dsimp only [y₁]; wram_simp [hqt_y]; rfl,
        by dsimp only [y₁, u]; wram_simp [hrE_y]; simp [rowPre],
        fun _ hi => absurd hi (by simp [rowPre]),
        fun _ _ => rfl⟩
    have hcolBody (w_st : Data 34) (hw_st : PC (w_st.regs idx) w_st)
        (hv_lt : w_st.regs idx < r) :
        ∃ w', ExecWithin w buildCSRColBody w_st w' 7 ∧ PC (w_st.regs idx + 1) w' ∧
          w'.regs idx = w_st.regs idx + 1 := by
      obtain ⟨_, hr_c, hqt_c, hrE_c, hed_c, hf_c⟩ := hw_st
      let v : Fin r := ⟨w_st.regs idx, hv_lt⟩
      have hmul_lt : u.val * r + w_st.regs idx < m * r := by
        calc u.val * r + w_st.regs idx < u.val * r + r := by omega
          _ = (u.val + 1) * r := by ring
          _ ≤ m * r := Nat.mul_le_mul_right r (by dsimp only [u]; omega)
      have hmat_uv : w_st.mem (matBase + u.val * r + w_st.regs idx) =
          if G (u, v) then 1 else 0 := by
        rw [hf_c _ (by omega)]
        dsimp only [y₁, u] at hmul_lt ⊢
        wram_simp [hlow_y (matBase + y.regs qHead * r + w_st.regs idx) (by omega)]
        simpa [Nat.add_assoc, u] using hmat u v
      have hw_one : w_st.regs one = 1 := by
        rw [hr_c one (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp [hy_one]
      have hw_zero : w_st.regs zero = 0 := by
        rw [hr_c zero (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp [hy_zero]
      have hw_bEdges : w_st.regs bEdgesReg = bOff + m + 1 := by
        rw [hr_c bEdgesReg (by decide) (by decide) (by decide)]
        dsimp only [y₁]; wram_simp [hy_bEdges]
      have hpre_succ : rowPre (w_st.regs idx + 1) =
          if G (u, v) then rowPre (w_st.regs idx) ++ [v] else rowPre (w_st.regs idx) := by
        dsimp only [rowPre]
        rw [List.take_succ_finRange hv_lt, List.filter_append]
        cases h : G (u, v) <;> simp [v, h]
      refine WP.exists_execWithin ?_
      unfold buildCSRColBody
      cases hG : G (u, v)
      · simp only [hG, Bool.false_eq_true, ↓reduceIte] at hmat_uv hpre_succ
        wram_exec [hqt_c, hw_one, hw_zero, hmat_uv]
        refine ⟨⟨by omega, fun i hi hne1 hne2 => by wram_simp [hr_c i hi hne1 hne2],
          by wram_simp; omega, by wram_simp [hrE_c, hpre_succ],
          hpre_succ ▸ hed_c, fun a ha => by wram_simp [hf_c a ha]⟩,
          by wram_simp⟩
      · simp only [hG, ↓reduceIte] at hmat_uv hpre_succ
        have hlen_lt_adj : (rowPre (w_st.regs idx)).length < (sInst.adj u).length := by
          have hle1 := hrowPre_sub (w_st.regs idx + 1)
          rw [hpre_succ, List.length_append, List.length_singleton] at hle1
          omega
        wram_exec [hqt_c, hw_one, hw_bEdges, hrE_c, hmat_uv]
        refine ⟨⟨by omega, fun i hi hne1 hne2 => by wram_simp [hr_c i hi hne1 hne2],
          by wram_simp; omega,
          by wram_simp; rw [hpre_succ, List.length_append, List.length_singleton]; omega,
          fun i hi => ?_, fun a ha => by wram_simp [hf_c a ha]⟩,
          by wram_simp⟩
        simp only [hpre_succ, List.length_append, List.length_singleton] at hi ⊢
        by_cases hi_lt : i < (rowPre (w_st.regs idx)).length
        · rw [List.getElem_append_left hi_lt]
          wram_simp [hed_c i hi_lt]
        · obtain rfl : i = (rowPre (w_st.regs idx)).length := by omega
          simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton, v]
          wram_simp
    have hy₁_idx : y₁.regs idx = 0 := by dsimp only [y₁]; wram_simp
    obtain ⟨y₂, hl_col, hPCr, _⟩ := ExecWithin.loop_count PC
      (fun w_st hw_st => by
        rw [hw_st.2.1 rr (by decide) (by decide) (by decide)]
        dsimp only [y₁]; wram_simp [hy_rr])
      hcolBody (x := y₁) (by rw [hy₁_idx]; exact Nat.zero_le r) (by rw [hy₁_idx]; exact hPC₀)
    rw [hy₁_idx, Nat.sub_zero] at hl_col
    obtain ⟨_, hr_c2, hqt_c2, hrE_c2, hed_c2, hf_c2⟩ := hPCr
    have hrowPre_full : rowPre r = sInst.adj u := by
      dsimp only [rowPre, sInst, exactBipAdj]
      rw [List.take_of_length_le (by simp)]
    have hy₂_qh : y₂.regs qHead = y.regs qHead := by
      rw [hr_c2 qHead (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp
    have hy₂_one : y₂.regs one = 1 := by
      rw [hr_c2 one (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp [hy_one]
    have he_post_row : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34) y₂
        (y₂.set qHead (y.regs qHead + 1)) 1 := by
      refine WP.execWithin ?_
      wram_exec [hy₂_qh, hy₂_one]
      rfl
    refine ⟨_, (he_pre_row.seq (hl_col.seq he_post_row)).mono (by omega),
      ⟨by omega, fun i hi hne => ?_, ?_, ?_, fun u' hu' => ?_, fun u' hu' {i} hi => ?_,
        fun a ha => ?_⟩, by wram_simp⟩
    · wram_simp
      rw [hr_c2 i (by omega) hne (by intro h; subst h; simp at hi)]
      dsimp only [y₁]; wram_simp [hr_y i hi hne]
    · wram_simp [hqt_c2]
      change matBase + u.val * r + r = matBase + (u.val + 1) * r
      ring
    · wram_simp [hrE_c2]
      rw [hrowPre_full, ← hoff_succ]
    · dsimp only [Data.set]
      rw [hf_c2 _ (by omega)]
      dsimp only [y₁, u]
      by_cases heq_u : u' = y.regs qHead
      · subst heq_u; wram_simp
      · wram_simp; exact hoff_y u' (by omega)
    · dsimp only [Data.set]
      by_cases heq_u : u' = u
      · subst heq_u
        simpa [hrowPre_full] using hed_c2 i (hrowPre_full.symm ▸ hi)
      · have hu'_lt : u'.val < u.val :=
          Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hu') fun h => heq_u (Fin.ext h)
        have hle_end : sInst.offset (u'.val + 1) ≤ sInst.offset u.val :=
          sInst.offset_mono hu'_lt
        have hoff_u'_succ : sInst.offset (u'.val + 1) =
            sInst.offset u'.val + (sInst.adj u').length := sInst.offset_succ u'.isLt
        rw [hf_c2 _ (by omega)]
        dsimp only [y₁]
        wram_simp
        exact hedge_y u' hu'_lt hi
    · dsimp only [Data.set]
      rw [hf_c2 a (by omega)]
      dsimp only [y₁]
      wram_simp [hlow_y a ha]
  have hs₀_qh : s₀.regs qHead = 0 := by dsimp only [s₀]; wram_simp
  obtain ⟨y_end, hl_row, hPRm, _⟩ := ExecWithin.loop_count PR
    (fun y hy => by
      rw [hy.2.1 rm (by decide) (by decide)]
      dsimp only [s₀]; wram_simp [hrm])
    hrowBody (x := s₀) (by rw [hs₀_qh]; exact Nat.zero_le m) (by rw [hs₀_qh]; exact hPR₀)
  rw [hs₀_qh, Nat.sub_zero] at hl_row
  obtain ⟨_, hr_m, _, hrE_m, hoff_m, hedge_m, _⟩ := hPRm
  have hend_bOff : y_end.regs bOffReg = bOff := by
    wram_simp [hr_m bOffReg (by decide) (by decide), s₀, hbOff]
  have hend_rm : y_end.regs rm = m := by
    wram_simp [hr_m rm (by decide) (by decide), s₀, hrm]
  let y_last := (y_end.set addr (bOff + m)).write (bOff + m) (sInst.offset m)
  have he_last : ExecWithin w
      (.seq (ram[ addr ← bOffReg + rm ]) (ram[ *addr ← rE ]) : Code .standard 34)
      y_end y_last 2 := by
    refine WP.execWithin ?_
    wram_exec [hend_bOff, hend_rm, hrE_m]
    rfl
  have hlast_reg (i : Fin 34) (hi : i.val < 22) (hne : i ≠ rE) : y_last.regs i = s₀.regs i := by
    have : i ≠ addr := fun h => by subst h; simp at hi
    calc y_last.regs i = y_end.regs i := by dsimp only [y_last]; wram_simp
      _ = s₀.regs i := hr_m i hi hne
  have hfit_init : Fits w (bOff + 7 * sInst.m + 5 * sInst.r + sInst.numEdges + 8) :=
    hfit.of_le (Nat.add_le_add_right (Nat.add_le_add_left hE_le _) 8)
  obtain ⟨z, he_init, hbz, hmem_z⟩ := exec_initBaseRegsFromCSR sInst y_last
    ((hlast_reg zero (by decide) (by decide)).trans (by dsimp only [s₀]; wram_simp [h0]))
    ((hlast_reg one (by decide) (by decide)).trans (by dsimp only [s₀]; wram_simp [h1]))
    ((hlast_reg two (by decide) (by decide)).trans (by dsimp only [s₀]; wram_simp [h2]))
    ((hlast_reg rm (by decide) (by decide)).trans (by dsimp only [s₀, sInst]; wram_simp [hrm]))
    ((hlast_reg rr (by decide) (by decide)).trans (by dsimp only [s₀, sInst]; wram_simp [hrr]))
    (by dsimp only [y_last]; wram_simp [hrE_m]; exact sInst.offset_m)
    ((hlast_reg bOffReg (by decide) (by decide)).trans (by dsimp only [s₀]; wram_simp [hbOff]))
    hfit_init
  have hcsrz : CSRMem sInst bOff z.mem :=
    { hoff := fun {u'} hu' => by
        rw [hmem_z]
        dsimp only [y_last]
        by_cases heq : u' = m
        · subst heq; wram_simp
        · wram_simp; exact hoff_m u' (by dsimp only [sInst] at hu'; omega)
      hedge := fun u' {i} hi => by
        have hed_u' := sInst.offset_add_lt_numEdges u' hi
        rw [hmem_z]
        dsimp only [y_last]
        wram_simp
        exact hedge_m u' u'.isLt hi }
  exact ⟨z, (he₀.seq (hl_row.seq (he_last.seq he_init))).mono (by nlinarith), hbz, hcsrz⟩

/-- Read header dimensions (`m`, and `r` if `isSquare = false` else `r = m`) from input memory,
compute `bOffReg := matBase + m * r` (with `matBase = 2` if `isSquare` else `3`), and convert
the row-major `m × r` `0/1` adjacency matrix starting at `matBase` into exact CSR arrays. -/
def matrixSetupCode (isSquare : Bool) : Code .standard 34 :=
  .seq (ram[ zero ← #0; one ← #1; two ← #2; addr ← #1; rm ← *addr ])
    (.seq (if isSquare then ram[ rr ← rm; val ← rm * rr; bOffReg ← two + val ]
           else ram[ addr ← #2; rr ← *addr; val ← rm * rr;
                     bOffReg ← #3; bOffReg ← bOffReg + val ])
      (buildCSRCode (if isSquare then 2 else 3)))

/-- Shared header-read and matrix-to-CSR conversion for dense (`isSquare = false`, header `[m, r]`)
and square poset (`isSquare = true`, header `[n]`) encodings. -/
theorem exec_matrixSetupCode {w m r : ℕ} (isSquare : Bool) (hsq : isSquare = true → m = r)
    (G : Fin m × Fin r → Bool) (input : List ℕ)
    (hm : (Data.init input : Data 34).mem 1 = m)
    (hr : isSquare = false → (Data.init input : Data 34).mem 2 = r)
    (hmat : ∀ (u : Fin m) (v : Fin r),
      (Data.init input : Data 34).mem ((if isSquare then 2 else 3) + (u.val * r + v.val)) =
        if G (u, v) then 1 else 0)
    (hfit : Fits w ((if isSquare then 2 else 3) + m * r + 7 * m + 5 * r + m * r + 8)) :
    ∃ y, ExecWithin w (matrixSetupCode isSquare) (Data.init input) y
        (9 * m * r + 8 * m + (if isSquare then 33 else 35)) ∧
      BaseRegs ⟨m, r, exactBipAdj G⟩ ((if isSquare then 2 else 3) + m * r) y ∧
      CSRMem ⟨m, r, exactBipAdj G⟩ ((if isSquare then 2 else 3) + m * r) y.mem := by
  obtain ⟨y₀, he_pre, h0, h1, h2, hrm, hmem₀⟩ : ∃ y₀, ExecWithin w
      (ram[ zero ← #0; one ← #1; two ← #2; addr ← #1; rm ← *addr ] : Code .standard 34)
      (Data.init input) y₀ 5 ∧
      y₀.regs zero = 0 ∧ y₀.regs one = 1 ∧ y₀.regs two = 2 ∧
      y₀.regs rm = m ∧ y₀.mem = (Data.init input : Data 34).mem := by
    have hfit2 : Fits w 2 := hfit.of_le (by cases isSquare <;> omega)
    refine WP.exists_execWithin ?_
    wram_exec [hm, hfit2]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₁, he_dim, h0', h1', h2', hrm', hrr', hbOff', hmem₁⟩ : ∃ y₁, ExecWithin w
      (if isSquare then ram[ rr ← rm; val ← rm * rr; bOffReg ← two + val ]
       else ram[ addr ← #2; rr ← *addr; val ← rm * rr;
                 bOffReg ← #3; bOffReg ← bOffReg + val ]) y₀ y₁ (if isSquare then 3 else 5) ∧
      y₁.regs zero = 0 ∧ y₁.regs one = 1 ∧ y₁.regs two = 2 ∧
      y₁.regs rm = m ∧ y₁.regs rr = r ∧
      y₁.regs bOffReg = (if isSquare then 2 else 3) + m * r ∧
      y₁.mem = (Data.init input : Data 34).mem := by
    refine WP.exists_execWithin ?_
    cases isSquare with
    | true =>
      obtain rfl := hsq rfl
      simp only [↓reduceIte]
      wram_exec [h2, hrm]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2],
        by wram_simp [hrm], by wram_simp, by wram_simp, hmem₀⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      wram_exec [hrm, hmem₀, hr rfl]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2],
        by wram_simp [hrm], by wram_simp, by wram_simp, hmem₀⟩
  obtain ⟨z, he_csr, hbz, hcsrz⟩ := exec_buildCSRCode (m := m) (r := r)
    (matBase := if isSquare then 2 else 3) (bOff := (if isSquare then 2 else 3) + m * r) G y₁
    h0' h1' h2' hrm' hrr' hbOff' le_rfl
    (fun u v => hmem₁.symm ▸ hmat u v) hfit
  exact ⟨z, (he_pre.seq (he_dim.seq he_csr)).mono (by cases isSquare <;> simp <;> omega), hbz,
    hcsrz⟩

end Cslib.Algorithms.WordRAM.HopcroftKarp
