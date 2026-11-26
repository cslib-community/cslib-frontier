/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Internal
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hopcroft–Karp queue-based breadth-first layering on the word RAM

Implements the `O(m + r + |E|)` word-RAM breadth-first layering subroutine `Internal.bfsCode`
used by `CslibFrontier.Algorithms.WordRAM.HopcroftKarp`, matching the pure specification
`Cslib.Algorithms.Lean.MaxFlow.hkBfs` ([HopcroftKarp1973]; [CLRS2009], Problem 26-6).

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.bfsCode`: marks matched left vertices, seeds
  layer `0` into the FIFO queue, and expands alternating layers until a free right vertex is
  reached or the queue empties.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.exec_bfsCode`: `O(m + r + |E|)` instruction
  bound and exact agreement with `hkBfs`.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp.Internal

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg

private def QueueSlice (inst : SparseInstance) (bOff start : ℕ) (xs : List (Fin inst.m))
    (mem : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < xs.length) →
    mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + start + i) = (xs[i]'hi).val

private theorem QueueSlice.snoc {inst : SparseInstance} {bOff start : ℕ}
    {xs : List (Fin inst.m)} {mem mem' : ℕ → ℕ} (h : QueueSlice inst bOff start xs mem)
    (u : Fin inst.m)
    (hpre : ∀ i < xs.length,
      mem' (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + start + i) =
        mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + start + i))
    (hlast :
      mem' (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + start + xs.length) = u.val) :
    QueueSlice inst bOff start (xs ++ [u]) mem' := by
  intro i hi
  have hi_lt : i < xs.length + 1 := by
    simpa only [List.length_append, List.length_singleton] using hi
  by_cases hlt : i < xs.length
  · rw [List.getElem_append_left hlt, hpre i hlt]
    exact h i hlt
  · have heqi : i = xs.length := by omega
    subst heqi
    simpa only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton] using
      hlast

private def markMLBody : Code .standard 34 := ram[
  addr ← bColMateReg + idx; val ← *addr;
  if val < rm then [ addr ← bMLReg + val; *addr ← one ] else [ tmp ← zero ];
  idx ← idx + one ]

private def markMLCode : Code .standard 34 :=
  .seq (clearAt bMLReg rm) (.seq (ram[ idx ← #0 ]) (.loop (.lt idx rr) markMLBody))

private theorem exec_markMLCode {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} (x : Data 34)
    (hb : BaseRegs inst bOff x) (hmate : MateMem inst bOff mate x.mem)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w markMLCode x y (4 * inst.m + 8 * inst.r + 7) ∧
      (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ u : Fin inst.m, y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + u.val) =
        if vget (hkMatchedLeft mate) u = true then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) → y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁, hr₁, hzero₁, hkeep₁⟩ := exec_clearAt bMLReg rm (by decide) (by decide) x
    hb.hzero hb.hone hb.hbML hb.hrm (hfit.of_le (by omega))
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ u : Fin inst.m, y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + u.val) =
        if vget (((List.finRange inst.r).take k).foldl (hkMarkStep mate)
            (Vector.replicate inst.m false)) u = true then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) → y.mem a = x.mem a)
  have he₀ : ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) y₁ (y₁.set idx 0) 1 :=
    WP.execWithin <| by
      wram_exec
      rfl
  have hP₀ : P 0 (y₁.set idx 0) :=
    ⟨fun i hi => by wram_simp [hr₁ i (by omega)], fun u => by
      simpa only [Data.set, List.take_zero, List.foldl_nil, vget_replicate, Bool.false_eq_true,
        ↓reduceIte] using hzero₁ u.val u.isLt,
      hkeep₁⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.r) :
      ∃ z, ExecWithin w markMLBody y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let v : Fin inst.r := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hcol_v :
        y.mem (bOff + inst.m + 1 + inst.numEdges + y.regs idx) = encodeOptFin (vget mate v) := by
      rw [hf _ (by omega)]
      exact hmate v
    have htk : (List.finRange inst.r).take (y.regs idx + 1) =
        (List.finRange inst.r).take (y.regs idx) ++ [v] := List.take_succ_finRange hlt
    refine WP.exists_execWithin ?_
    unfold markMLBody
    cases hmv : vget mate v with
    | none =>
      have henc : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
      have hnl : ¬inst.m < inst.m := Nat.lt_irrefl _
      wram_exec [hby.hbColMate, hby.hrm, hby.hzero, hby.hone, hcol_v, henc, hnl]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun u => ?_, fun a ha => by wram_simp [hf a ha]⟩,
        by wram_simp⟩
      wram_simp
      rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, hkMarkStep, hmv]
      exact hm u
    | some w₀ =>
      have henc : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
      have hwlt : w₀.val < inst.m := w₀.isLt
      wram_exec [hby.hbColMate, hby.hbML, hby.hrm, hby.hzero, hby.hone, hcol_v, henc, hwlt]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun u => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, hkMarkStep, hmv]
        rcases eq_or_ne u w₀ with rfl | hne
        · wram_simp
          simp
        · have hne_val : u.val ≠ w₀.val := fun h => hne (Fin.ext h)
          wram_simp
          rw [vget_vset_ne _ _ hne.symm]
          exact hm u
      · wram_simp
        exact hf a ha
  obtain ⟨y, hl, hPr, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rr (by decide)).trans hb.hrr) hbody
    (x := y₁.set idx 0) (by simp) (by simpa using hP₀)
  refine ⟨y, (he₁.seq (he₀.seq hl)).mono (by simp; omega), hPr.1, fun u => ?_, hPr.2.2⟩
  have hu_eq := hPr.2.1 u
  rwa [List.take_of_length_le List.length_finRange.le] at hu_eq

private def seedBfsBody : Code .standard 34 := ram[
  addr ← bMLReg + idx; val ← *addr;
  if val = zero then [
    addr ← bDistReg + idx; *addr ← one;
    addr ← bQueueReg + qTail; *addr ← idx;
    qTail ← qTail + one
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def seedBfsCode : Code .standard 34 :=
  .seq (clearAt bDistReg rm)
    (.seq (ram[ qHead ← #0; qTail ← #0; rk ← #0; rfound ← #0; idx ← #0 ])
      (.seq (.loop (.lt idx rm) seedBfsBody)
        (ram[ if qHead < qTail then [ active ← one ] else [ active ← zero ] ])))

private theorem exec_seedBfsCode {w bOff : ℕ} {inst : SparseInstance}
    {ml : Vector Bool inst.m} (x : Data 34) (hb : BaseRegs inst bOff x)
    (hml : ∀ u : Fin inst.m, x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + u.val) =
      if vget ml u = true then 1 else 0)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let p := (List.finRange inst.m).foldl (hkBfsInitStep ml) (Vector.replicate inst.m none, [])
    ∃ y, ExecWithin w seedBfsCode x y (15 * inst.m + 14) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem inst bOff p.1 y.mem ∧
      QueueSlice inst bOff 0 p.2 y.mem ∧
      y.regs qHead = 0 ∧
      y.regs qTail = p.2.length ∧
      y.regs rk = 0 ∧
      y.regs rfound = 0 ∧
      y.regs active = (if p.2 = [] then 0 else 1) ∧
      p.2.Nodup ∧
      (∀ u : Fin inst.m, vget p.1 u ≠ none ↔ u ∈ p.2) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  intro p
  obtain ⟨y₁, he₁, hr₁, hzero₁, hkeep₁⟩ := exec_clearAt bDistReg rm (by decide) (by decide) x
    hb.hzero hb.hone hb.hbDist hb.hrm (hfit.of_le (by omega))
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ qHead ← #0; qTail ← #0; rk ← #0; rfound ← #0; idx ← #0 ] : Code .standard 34) y₁ s₀ 5 ∧
      s₀ = ((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0 :=
    WP.exists_execWithin <| by
      wram_exec
      rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let pk (k : ℕ) :=
    ((List.finRange inst.m).take k).foldl (hkBfsInitStep ml) (Vector.replicate inst.m none, [])
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem inst bOff (pk k).1 y.mem ∧
      QueueSlice inst bOff 0 (pk k).2 y.mem ∧
      y.regs qHead = 0 ∧
      y.regs qTail = (pk k).2.length ∧
      y.regs rk = 0 ∧
      y.regs rfound = 0 ∧
      (pk k).2.Nodup ∧
      (∀ x₀ ∈ (pk k).2, x₀.val < k) ∧
      (∀ u : Fin inst.m, vget (pk k).1 u ≠ none ↔ u ∈ (pk k).2) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + k) → y.mem a = x.mem a)
  have hP₀ : P 0 (((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0) :=
    ⟨fun i hi => by wram_simp [hr₁ i (by omega)],
      fun u => by simpa only [Data.set, pk, List.take_zero, List.foldl_nil, vget_replicate,
        encodeDist] using hzero₁ u.val u.isLt,
      fun _ hi => by simp [pk] at hi,
      by wram_simp, by wram_simp; simp [pk], by wram_simp, by wram_simp, by simp [pk],
      fun _ h => by simp [pk] at h, fun u => by simp [pk, vget_replicate],
      fun a ha => hkeep₁ a (by omega)⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.m) :
      ∃ z, ExecWithin w seedBfsBody y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hdM, hqM, hqh, hqt, hrk, hrf, hnd, hlt_mem, hiff, hf⟩ := hy
    let u : Fin inst.m := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hml_u : y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + y.regs idx) =
        if vget ml u = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hml u
    have hlen_le : (pk (y.regs idx)).2.length ≤ y.regs idx := by
      have hsub : (pk (y.regs idx)).2.Sublist ((List.finRange inst.m).take (y.regs idx)) := by
        have hgen : ∀ (ls : List (Fin inst.m))
            (st : Vector (Option ℕ) inst.m × List (Fin inst.m)),
            (ls.foldl (hkBfsInitStep ml) st).2.Sublist (st.2 ++ ls) := by
          intro ls
          induction ls with
          | nil => intro st; simp
          | cons a ls ih =>
            intro st
            simp only [List.foldl_cons, hkBfsInitStep]
            split_ifs
            · exact (ih st).trans ((List.sublist_cons_self a ls).append_left st.2)
            · simpa [List.append_assoc] using ih (vset st.1 a (some 0), st.2 ++ [a])
        simpa [pk] using hgen ((List.finRange inst.m).take (y.regs idx))
          (Vector.replicate inst.m none, [])
      exact hsub.length_le.trans (by simp)
    have htk : pk (y.regs idx + 1) = hkBfsInitStep ml (pk (y.regs idx)) u := by
      simp only [pk, List.take_succ_finRange hlt, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rfl
    refine WP.exists_execWithin ?_
    unfold seedBfsBody
    by_cases hmu : vget ml u = true
    · have hval1 : (if vget ml u = true then 1 else 0) = 1 := ite_eq_left hmu
      have hpk1 : pk (y.regs idx + 1) = pk (y.regs idx) := by
        rw [htk, hkBfsInitStep, ite_eq_left hmu]
      wram_exec [hby.hbML, hby.hzero, hby.hone, hml_u, hval1]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], ?_, ?_, by wram_simp [hqh], ?_,
        by wram_simp [hrk], by wram_simp [hrf], ?_, ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
      · intro w₀; wram_simp; rw [hpk1]; exact hdM w₀
      · intro i hi; wram_simp; simp only [hpk1] at hi ⊢; exact hqM i hi
      · wram_simp; rw [hpk1]; exact hqt
      · rw [hpk1]; exact hnd
      · intro x₀ hx₀; rw [hpk1] at hx₀; exact Nat.lt_succ_of_lt (hlt_mem x₀ hx₀)
      · intro w₀; rw [hpk1]; exact hiff w₀
      · wram_simp; exact hf a (by omega)
    · have hval0 : (if vget ml u = true then 1 else 0) = 0 := ite_eq_right hmu
      have hu_not_mem : u ∉ (pk (y.regs idx)).2 := fun h => Nat.lt_irrefl _ (hlt_mem u h)
      have hpk0 : pk (y.regs idx + 1) =
          (vset (pk (y.regs idx)).1 u (some 0), (pk (y.regs idx)).2 ++ [u]) := by
        rw [htk, hkBfsInitStep, ite_eq_right hmu]
      wram_exec [hby.hbML, hby.hbDist, hby.hbQueue, hby.hzero, hby.hone, hml_u, hval0, hqt]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], ?_, ?_, by wram_simp [hqh], ?_,
        by wram_simp [hrk], by wram_simp [hrf], ?_, ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
      · rw [hpk0]
        exact hdM.vset u (some 0) (by wram_simp; rfl) fun w₀ hne => by
          have := w₀.isLt
          have hne_val : w₀.val ≠ y.regs idx := fun h => hne (Fin.ext h)
          wram_simp
      · rw [hpk0]
        exact hqM.snoc u (fun i hi => by wram_simp) (by wram_simp; rfl)
      · wram_simp
        rw [hpk0]
        simp
      · rw [hpk0]
        exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton u, fun a ha b hb hab => by
          obtain rfl := List.mem_singleton.mp hb; subst hab; exact hu_not_mem ha⟩
      · intro x₀ hx₀
        rw [hpk0, List.mem_append, List.mem_singleton] at hx₀
        rcases hx₀ with hx₀ | rfl
        · exact Nat.lt_succ_of_lt (hlt_mem x₀ hx₀)
        · exact Nat.lt_succ_self _
      · intro w₀
        rw [hpk0]
        rcases eq_or_ne w₀ u with rfl | hne
        · simp
        · simp [vget_vset_ne _ _ hne.symm, hiff w₀, hne]
      · wram_simp
        exact hf a (by omega)
  obtain ⟨y₂, hl, hPm⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rm (by decide)).trans hb.hrm) hbody
    (x := ((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0) (by simp)
    (by simpa using hP₀)
  obtain ⟨⟨hr₂, hdM₂, hqM₂, hqh₂, hqt₂, hrk₂, hrf₂, hnd₂, _, hiff₂, hf₂⟩, _⟩ := hPm
  have hfull : pk inst.m = p := by
    dsimp only [pk, p]
    rw [List.take_of_length_le (by simp)]
  rw [hfull] at hdM₂ hqM₂ hqt₂ hnd₂ hiff₂
  have hb₂ : BaseRegs inst bOff y₂ := hb.of_eq fun i hi => hr₂ i (by omega)
  set y₃ := y₂.set active (if p.2 = [] then 0 else 1) with hy₃
  have he_act : ExecWithin w
      (ram[ if qHead < qTail then [ active ← one ] else [ active ← zero ] ] : Code .standard 34)
      y₂ y₃ 3 := WP.execWithin <| by
    by_cases hne : 0 < p.2.length
    · wram_exec [hqh₂, hqt₂, hb₂.hone, hb₂.hzero, hne]
      simp [hy₃, List.ne_nil_of_length_pos hne]
    · wram_exec [hqh₂, hqt₂, hb₂.hone, hb₂.hzero, hne]
      simp [hy₃, List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_not_pos hne)]
  refine ⟨y₃, (he₁.seq (he₀.seq (hl.seq he_act))).mono (by simp; omega),
    fun i hi => by wram_simp [hy₃, hr₂ i hi], hdM₂, hqM₂,
    by wram_simp [hy₃, hqh₂],
    by wram_simp [hy₃, hqt₂],
    by wram_simp [hy₃, hrk₂],
    by wram_simp [hy₃, hrf₂],
    by wram_simp [hy₃], hnd₂, hiff₂,
    fun a ha => hf₂ a (by omega)⟩

private def bfsEdgeBody : Code .standard 34 := ram[
  addr ← bEdgesReg + idx; val ← *addr;
  addr ← bColMateReg + val; val2 ← *addr;
  if val2 = rm then [ rfound ← one ] else [
    addr ← bDistReg + val2; tmp ← *addr;
    if tmp = zero then [
      tmp ← rk + two;
      addr ← bDistReg + val2; *addr ← tmp;
      addr ← bQueueReg + qTail; *addr ← val2;
      qTail ← qTail + one
    ] else [ tmp ← zero ]
  ];
  idx ← idx + one ]

private def bfsVertexBody : Code .standard 34 :=
  .seq (ram[
    addr ← bQueueReg + qHead; val ← *addr;
    qHead ← qHead + one;
    addr ← bOffReg + val; idx ← *addr;
    addr ← addr + one; limit ← *addr ])
  (.loop (.lt idx limit) bfsEdgeBody)

private def bfsLayerBody : Code .standard 34 :=
  .seq (ram[ layerEnd ← qTail ])
    (.seq (.loop (.lt qHead layerEnd) bfsVertexBody)
      (ram[
        if rfound = one then [ active ← zero ] else [
          if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ]
        ] ]))

/-- Queue-based breadth-first layering (`O(m + r + |E|)` instructions per round). -/
def bfsCode : Code .standard 34 :=
  .seq markMLCode (.seq seedBfsCode (.loop (.eq active one) bfsLayerBody))

private def bfsVertWeight (inst : SparseInstance) (u : Fin inst.m) : ℕ :=
  18 * (inst.adj u).length + 11

private theorem sum_bfsVertWeight (inst : SparseInstance) :
    ∑ u, bfsVertWeight inst u = 18 * inst.numEdges + 11 * inst.m := by
  simp [bfsVertWeight, SparseInstance.numEdges, bipAdjSteps, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Nat.mul_comm]

private theorem exec_bfsEdgeLoop {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} (j qh le : ℕ)
    (u : Fin inst.m) (s : HKBfsState inst.m) (queued : List (Fin inst.m))
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem inst bOff mate x.mem)
    (hdM : DistMem inst bOff s.dist x.mem)
    (hq_pre : QueueSlice inst bOff qh queued x.mem)
    (hq_next : QueueSlice inst bOff le s.next x.mem)
    (hle_eq : qh + queued.length = le)
    (hidx : x.regs idx = inst.offset u.val)
    (hlim : x.regs limit = inst.offset (u.val + 1))
    (hrk : x.regs rk = j)
    (hrf : x.regs rfound = (if s.found then 1 else 0))
    (hqh : x.regs qHead = qh)
    (hle : x.regs layerEnd = le)
    (hqt : x.regs qTail = le + s.next.length)
    (hact : x.regs active = 1)
    (hiff : ∀ w₀ : Fin inst.m, vget s.dist w₀ = none → w₀ ∉ s.next)
    (hqt_bound : le + (Finset.univ.filter fun w₀ => vget s.dist w₀ = none).card + s.next.length ≤
      inst.m)
    (hj_le : j ≤ inst.m + 1)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let sF := (inst.adj u).foldl (hkBfsStep inst.graph mate j u) s
    ∃ y, ExecWithin w (.loop (.lt idx limit) bfsEdgeBody) x y (18 * (inst.adj u).length + 2) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem inst bOff sF.dist y.mem ∧
      QueueSlice inst bOff qh queued y.mem ∧
      QueueSlice inst bOff le sF.next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if sF.found then 1 else 0) ∧
      y.regs qHead = qh ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + sF.next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget sF.dist w₀ = none → w₀ ∉ sF.next) ∧
      le + (Finset.univ.filter fun w₀ => vget sF.dist w₀ = none).card + sF.next.length ≤ inst.m ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  intro sF
  let sk (k : ℕ) : HKBfsState inst.m :=
    ((inst.adj u).take (k - inst.offset u.val)).foldl (hkBfsStep inst.graph mate j u) s
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ u.isLt
  let P (k : ℕ) (y : Data 34) : Prop :=
    inst.offset u.val ≤ k ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs limit = inst.offset (u.val + 1) ∧
      DistMem inst bOff (sk k).dist y.mem ∧
      QueueSlice inst bOff qh queued y.mem ∧
      QueueSlice inst bOff le (sk k).next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if (sk k).found then 1 else 0) ∧
      y.regs qHead = qh ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + (sk k).next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget (sk k).dist w₀ = none → w₀ ∉ (sk k).next) ∧
      le + (Finset.univ.filter fun w₀ => vget (sk k).dist w₀ = none).card + (sk k).next.length ≤
        inst.m ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a)
  have hsk₀ : sk (x.regs idx) = s := by simp [sk, hidx]
  have hP₀ : P (x.regs idx) x := by
    dsimp only [P]
    rw [hsk₀]
    exact ⟨by omega, fun _ _ => rfl, hlim, hdM, hq_pre, hq_next, hrk, hrf, hqh, hle, hqt, hact,
      hiff, hqt_bound, fun _ _ => rfl⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.offset (u.val + 1)) :
      ∃ z, ExecWithin w bfsEdgeBody y z 16 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hge, hr, hlim_y, hdMy, hq_pre_y, hq_next_y, hrk_y, hrf_y, hqh_y, hle_y, hqt_y,
      hact_y, hiff_y, hbound_y, hf_y⟩ := hy
    let t := y.regs idx - inst.offset u.val
    have ht_lt : t < (inst.adj u).length := by dsimp only [t]; omega
    let v : Fin inst.r := (inst.adj u)[t]'ht_lt
    have hv_lt := v.isLt
    have hGu : inst.graph (u, v) = true := decide_eq_true (List.getElem_mem ht_lt)
    have hsk_step : sk (y.regs idx + 1) = hkBfsStep inst.graph mate j u (sk (y.regs idx)) v := by
      have hsub : y.regs idx + 1 - inst.offset u.val = t + 1 := by dsimp only [t]; omega
      simp only [sk, hsub, List.take_add_one, List.getElem?_eq_getElem ht_lt, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, v]
      rfl
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hp_eq : y.regs idx = inst.offset u.val + t := by dsimp only [t]; omega
    have hlt_E := inst.offset_add_lt_numEdges u ht_lt
    have hoff_u1_le := inst.offset_le_numEdges (u.val + 1)
    have hedge_y : y.mem (bOff + inst.m + 1 + y.regs idx) = v.val := by
      rw [hf_y _ (by omega), hp_eq]
      exact hcsr.hedge u ht_lt
    have hmate_v :
        y.mem (bOff + inst.m + 1 + inst.numEdges + v.val) = encodeOptFin (vget mate v) := by
      rw [hf_y _ (by omega)]
      exact hmate v
    have no_alloc_step (z : Data 34)
        (hdist_eq : (sk (y.regs idx + 1)).dist = (sk (y.regs idx)).dist)
        (hnext_eq : (sk (y.regs idx + 1)).next = (sk (y.regs idx)).next)
        (hr_z : ∀ i : Fin 34, i.val < 20 → z.regs i = y.regs i)
        (hlim_z : z.regs limit = inst.offset (u.val + 1))
        (hrk_z : z.regs rk = j)
        (hrf_z : z.regs rfound = if (sk (y.regs idx + 1)).found then 1 else 0)
        (hqh_z : z.regs qHead = qh) (hle_z : z.regs layerEnd = le)
        (hqt_z : z.regs qTail = le + (sk (y.regs idx)).next.length)
        (hact_z : z.regs active = 1) (hidx_z : z.regs idx = y.regs idx + 1)
        (hmem_z : z.mem = y.mem) :
        P (y.regs idx + 1) z ∧ z.regs idx = y.regs idx + 1 :=
      ⟨⟨by omega, fun i hi => (hr_z i hi).trans (hr i hi), hlim_z,
        by rw [hdist_eq, hmem_z]; exact hdMy, by rw [hmem_z]; exact hq_pre_y,
        by rw [hnext_eq, hmem_z]; exact hq_next_y, hrk_z, hrf_z, hqh_z, hle_z,
        by rw [hnext_eq]; exact hqt_z, hact_z, by rw [hdist_eq, hnext_eq]; exact hiff_y,
        by rw [hdist_eq, hnext_eq]; exact hbound_y, fun a ha => by rw [hmem_z]; exact hf_y a ha⟩,
        hidx_z⟩
    refine WP.exists_execWithin ?_
    unfold bfsEdgeBody
    cases hmv : vget mate v with
    | none =>
      have henc : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
      wram_exec [hby.hbEdges, hby.hbColMate, hby.hrm, hby.hone, hedge_y, hmate_v, henc]
      exact no_alloc_step _ (by rw [hsk_step]; simp [hkBfsStep, hGu, hmv])
        (by rw [hsk_step]; simp [hkBfsStep, hGu, hmv]) (fun _ _ => by wram_simp)
        (by wram_simp [hlim_y]) (by wram_simp [hrk_y])
        (by wram_simp; rw [hsk_step]; simp [hkBfsStep, hGu, hmv])
        (by wram_simp [hqh_y]) (by wram_simp [hle_y]) (by wram_simp [hqt_y])
        (by wram_simp [hact_y]) (by wram_simp) rfl
    | some w₀ =>
      have hw_lt := w₀.isLt
      have henc : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
      have hw_ne : w₀.val ≠ inst.m := ne_of_lt hw_lt
      have hdist_w : y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val) =
          encodeDist (vget (sk (y.regs idx)).dist w₀) :=
        hdMy w₀
      cases hdw : vget (sk (y.regs idx)).dist w₀ with
      | none =>
        have henc_d : encodeDist (vget (sk (y.regs idx)).dist w₀) = 0 := by
          simp [hdw, encodeDist]
        have hw_in_filt : w₀ ∈ Finset.univ.filter
            (fun x₀ => vget (sk (y.regs idx)).dist x₀ = none) := by simp [hdw]
        have := Finset.card_pos.mpr ⟨w₀, hw_in_filt⟩
        have hqt_lt_m : le + (sk (y.regs idx)).next.length < inst.m := by omega
        wram_exec [hby.hbEdges, hby.hbColMate, hby.hbDist, hby.hbQueue, hby.hrm, hby.hzero,
          hby.hone, hby.htwo, hrk_y, hqt_y, hedge_y, hmate_v, henc, hw_ne, hdist_w, henc_d]
        have hcard_erase :
            (Finset.univ.filter
              (fun x₀ => vget (vset (sk (y.regs idx)).dist w₀ (some (j + 1))) x₀ = none)).card +
              1 =
            (Finset.univ.filter (fun x₀ => vget (sk (y.regs idx)).dist x₀ = none)).card := by
          rw [← Finset.card_erase_add_one hw_in_filt]
          congr 2
          ext x₀
          rcases eq_or_ne x₀ w₀ with rfl | hne
          · simp
          · simp [hne, vget_vset_ne _ _ hne.symm]
        refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hlim_y], ?_,
          ?_, ?_, by wram_simp [hrk_y], ?_, by wram_simp [hqh_y], by wram_simp [hle_y],
          ?_, by wram_simp [hact_y], ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
        · rw [hsk_step]
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte]
          exact hdMy.vset w₀ (some (j + 1)) (by wram_simp; rfl) fun x₀ hne => by
            have := x₀.isLt
            have hne_val : x₀.val ≠ w₀.val := fun h => hne (Fin.ext h)
            wram_simp
        · intro i hi
          wram_simp
          exact hq_pre_y i hi
        · rw [hsk_step]
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte]
          exact hq_next_y.snoc w₀ (fun i hi => by wram_simp) (by wram_simp)
        · wram_simp [hrf_y]; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw]
        · wram_simp; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw]; omega
        · intro x₀ hx₀
          rw [hsk_step] at hx₀ ⊢
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte] at hx₀ ⊢
          have hxne : x₀ ≠ w₀ := fun h => by subst h; simp at hx₀
          rw [vget_vset_ne _ _ hxne.symm] at hx₀
          intro hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hiff_y x₀ hx₀ hmem
          · exact hxne (List.mem_singleton.mp hmem)
        · rw [hsk_step]
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte, List.length_append,
            List.length_singleton]
          omega
        · wram_simp
          exact hf_y a ha
      | some d₀ =>
        have henc_ne : encodeDist (vget (sk (y.regs idx)).dist w₀) ≠ 0 := by
          simp [hdw, encodeDist]
        wram_exec [hby.hbEdges, hby.hbColMate, hby.hbDist, hby.hrm, hby.hzero, hby.hone,
          hedge_y, hmate_v, henc, hw_ne, hdist_w, henc_ne]
        exact no_alloc_step _ (by rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw])
          (by rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw]) (fun _ _ => by wram_simp)
          (by wram_simp [hlim_y]) (by wram_simp [hrk_y])
          (by wram_simp [hrf_y]; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw])
          (by wram_simp [hqh_y]) (by wram_simp [hle_y]) (by wram_simp [hqt_y])
          (by wram_simp [hact_y]) (by wram_simp) rfl
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.2.1) hbody
    (x := x) (by rw [hidx]; omega) hP₀
  have hsk_end : sk (inst.offset (u.val + 1)) = sF := by
    have hsub : inst.offset (u.val + 1) - inst.offset u.val = (inst.adj u).length := by omega
    simp [sk, hsub, List.take_of_length_le (le_refl _), sF]
  dsimp only [P] at hPend
  rw [hsk_end] at hPend
  obtain ⟨_, hr, _, hdM', hq_pre', hq_next', hrk', hrf', hqh', hle', hqt', hact',
    hiff', hbound', hf'⟩ := hPend
  exact ⟨y, hl.mono (by rw [hidx, hoff_succ]; omega), hr, hdM', hq_pre', hq_next',
    hrk', hrf', hqh', hle', hqt', hact', hiff', hbound', hf'⟩

private theorem exec_bfsFrontierLoop {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} (j qh le : ℕ)
    (frontier : List (Fin inst.m)) (s : HKBfsState inst.m)
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem inst bOff mate x.mem)
    (hdM : DistMem inst bOff s.dist x.mem)
    (hq_pre : QueueSlice inst bOff qh frontier x.mem)
    (hq_next : QueueSlice inst bOff le s.next x.mem)
    (hle_eq : qh + frontier.length = le)
    (hrk : x.regs rk = j)
    (hrf : x.regs rfound = (if s.found then 1 else 0))
    (hqh : x.regs qHead = qh)
    (hle : x.regs layerEnd = le)
    (hqt : x.regs qTail = le + s.next.length)
    (hact : x.regs active = 1)
    (hiff : ∀ w₀ : Fin inst.m, vget s.dist w₀ = none → w₀ ∉ s.next)
    (hqt_bound : le + (Finset.univ.filter fun w₀ => vget s.dist w₀ = none).card + s.next.length ≤
      inst.m)
    (hj_le : j ≤ inst.m + 1)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let sF := hkBfsLayer inst.graph inst.adj mate j frontier s
    ∃ y, ExecWithin w (.loop (.lt qHead layerEnd) bfsVertexBody) x y
        ((frontier.map (bfsVertWeight inst)).sum + 2) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem inst bOff sF.dist y.mem ∧
      QueueSlice inst bOff le sF.next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if sF.found then 1 else 0) ∧
      y.regs qHead = le ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + sF.next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget sF.dist w₀ = none → w₀ ∉ sF.next) ∧
      le + (Finset.univ.filter fun w₀ => vget sF.dist w₀ = none).card + sF.next.length ≤ inst.m ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  induction frontier generalizing qh s x with
  | nil =>
    have hc : ¬(Cond.lt qHead layerEnd).Holds x := by
      simp [Cond.holds_lt, hqh, hle, ← hle_eq]
    exact ⟨x, ExecWithin.loop_exit hc, fun _ _ => rfl, hdM, hq_next, hrk, hrf,
      by simp only [List.length_nil] at hle_eq; omega, hle, hqt, hact, hiff, hqt_bound,
      fun _ _ => rfl⟩
  | cons u us ih =>
    have hu_lt := u.isLt
    have hle_cons : qh + (us.length + 1) = le := by simpa only [List.length_cons] using hle_eq
    have hc : (Cond.lt qHead layerEnd).Holds x := by simp only [Cond.holds_lt, hqh, hle]; omega
    have hq_u : x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + qh) = u.val := by
      simpa using hq_pre 0 (Nat.zero_lt_succ _)
    have hq_us : QueueSlice inst bOff (qh + 1) us x.mem := fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hq_pre (i + 1) (Nat.succ_lt_succ hi)
    have hoff_u : x.mem (bOff + u.val) = inst.offset u.val := hcsr.hoff (le_of_lt hu_lt)
    have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.hoff hu_lt
    set x₁ := ((((((x.set addr (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + qh)).set
      val u.val).set qHead (qh + 1)).set addr (bOff + u.val)).set idx (inst.offset u.val)).set
      addr (bOff + u.val + 1)).set limit (inst.offset (u.val + 1)) with hx₁
    have he_set : ExecWithin w (ram[
        addr ← bQueueReg + qHead; val ← *addr;
        qHead ← qHead + one;
        addr ← bOffReg + val; idx ← *addr;
        addr ← addr + one;
        limit ← *addr ] : Code .standard 34) x x₁ 7 :=
      WP.execWithin <| by
        wram_exec [hb.hbQueue, hb.hbOff, hb.hone, hqh, hq_u, hoff_u, hoff_u1]
        rfl
    have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => by wram_simp [hx₁]
    obtain ⟨x₂, he_edges, hr₂, hdM₂, hq_us₂, hq_next₂, hrk₂, hrf₂, hqh₂, hle₂, hqt₂, hact₂,
      hiff₂, hbound₂, hf₂⟩ :=
      exec_bfsEdgeLoop j (qh + 1) le u s us x₁ hb₁ hcsr hmate hdM hq_us hq_next (by omega)
        (by wram_simp [hx₁])
        (by wram_simp [hx₁])
        (by wram_simp [hx₁, hrk])
        (by wram_simp [hx₁, hrf])
        (by wram_simp [hx₁])
        (by wram_simp [hx₁, hle])
        (by wram_simp [hx₁, hqt])
        (by wram_simp [hx₁, hact])
        hiff hqt_bound hj_le hfit
    have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
    obtain ⟨y, he_rest, hr₃, hdM₃, hq_next₃, hrk₃, hrf₃, hqh₃, hle₃, hqt₃, hact₃,
      hiff₃, hbound₃, hf₃⟩ :=
      ih (qh + 1) _ x₂ hb₂ (hcsr.of_outside fun a ha => hf₂ a (by omega))
        (hmate.of_outside fun a ha => hf₂ a (by omega)) hdM₂ hq_us₂ hq_next₂ (by omega)
        hrk₂ hrf₂ hqh₂ hle₂ hqt₂ hact₂ hiff₂ hbound₂
    refine ⟨y, (ExecWithin.loop_iter hc (he_set.seq he_edges) he_rest).mono ?_,
      fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (by wram_simp [hx₁])),
      hdM₃, hq_next₃, hrk₃, hrf₃, hqh₃, hle₃, hqt₃, hact₃, hiff₃, hbound₃,
      fun a ha => (hf₃ a ha).trans (hf₂ a ha)⟩
    simp only [List.map_cons, List.sum_cons, bfsVertWeight]
    omega

private theorem exec_bfsLayersLoop {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (fuel j qh : ℕ) (dist : Vector (Option ℕ) inst.m) (frontier : List (Fin inst.m))
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem inst bOff mate x.mem)
    (hdM : DistMem inst bOff dist x.mem)
    (hq_pre : QueueSlice inst bOff qh frontier x.mem)
    (hrk : x.regs rk = j)
    (hrf : x.regs rfound = 0)
    (hqh : x.regs qHead = qh)
    (hqt : x.regs qTail = qh + frontier.length)
    (hact : x.regs active = (if frontier = [] then 0 else 1))
    (hfuel : inst.m + 1 ≤ fuel + qh)
    (hbound : qh + frontier.length + (Finset.univ.filter fun w₀ => vget dist w₀ = none).card ≤
      inst.m)
    (hj_le : j + fuel ≤ inst.m + 1)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let res := hkBfsLoop inst.graph inst.adj mate fuel j dist frontier
    ∃ y, ExecWithin w (.loop (.eq active one) bfsLayerBody) x y
        (10 * fuel + (frontier.map (bfsVertWeight inst)).sum +
          vecPotential (· = none) (bfsVertWeight inst) dist + 2) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem inst bOff res.dist y.mem ∧
      y.regs rk = res.k ∧
      y.regs rfound = (if res.found then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  induction fuel generalizing j qh dist frontier x with
  | zero =>
    obtain rfl : frontier = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc : ¬(Cond.eq active one).Holds x := by
      simpa [Cond.holds_eq, hact] using ne_of_ne_of_eq Nat.zero_ne_one hb.hone.symm
    exact ⟨x, (ExecWithin.loop_exit hc).mono (by omega), fun _ _ => rfl, hdM, hrk, hrf,
      fun _ _ => rfl⟩
  | succ fuel ih =>
    by_cases hnil : frontier = []
    · subst hnil
      have hc : ¬(Cond.eq active one).Holds x := by
        simpa [Cond.holds_eq, hact] using ne_of_ne_of_eq Nat.zero_ne_one hb.hone.symm
      exact ⟨x, (ExecWithin.loop_exit hc).mono (by omega), fun _ _ => rfl, hdM, hrk, hrf,
        fun _ _ => rfl⟩
    · have hpos_f : 0 < frontier.length := List.length_pos_iff.mpr hnil
      have hc : (Cond.eq active one).Holds x := by
        simpa [Cond.holds_eq, hact, hnil] using hb.hone.symm
      let le := qh + frontier.length
      have he_le : ExecWithin w (ram[ layerEnd ← qTail ] : Code .standard 34) x
          (x.set layerEnd le) 1 :=
        WP.execWithin <| by
          wram_exec [hqt]
          rfl
      have hb₁ : BaseRegs inst bOff (x.set layerEnd le) := hb.of_eq fun i hi => by wram_simp
      obtain ⟨x₂, he_front, hr₂, hdM₂, hq_next₂, hrk₂, hrf₂, hqh₂, hle₂, hqt₂, hact₂,
        _, hbound₂, hf₂⟩ :=
        exec_bfsFrontierLoop j qh le frontier ⟨dist, [], false⟩ (x.set layerEnd le) hb₁ hcsr
          hmate hdM hq_pre (fun _ hi => by simp at hi) rfl (by wram_simp [hrk])
          (by wram_simp [hrf]; simp) (by wram_simp [hqh]) (by wram_simp)
          (by wram_simp [hqt, le]; simp)
          (by wram_simp [hact, hnil]) (fun _ _ h => nomatch h)
          (by simp only [List.length_nil, Nat.add_zero, le]; exact hbound) (by omega) hfit
      set s := hkBfsLayer inst.graph inst.adj mate j frontier ⟨dist, [], false⟩ with hs_def
      have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
      have hpot := layerFold_potential inst.graph inst.adj mate (bfsVertWeight inst) j frontier
        ⟨dist, [], false⟩
      simp only [List.map_nil, List.sum_nil, Nat.add_zero, ← hs_def] at hpot
      have stop_of_tail (he_tail : ExecWithin w (ram[
          if rfound = one then [ active ← zero ] else [
            if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ] ] ] :
          Code .standard 34) x₂ (x₂.set active 0) 4)
          (hstop : s.found = true ∨ s.next.isEmpty = true) :
          ∃ y, ExecWithin w (.loop (.eq active one) bfsLayerBody) x y
              (10 * (fuel + 1) + (frontier.map (bfsVertWeight inst)).sum +
                vecPotential (· = none) (bfsVertWeight inst) dist + 2) ∧
            (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
            DistMem inst bOff
              (hkBfsLoop inst.graph inst.adj mate (fuel + 1) j dist frontier).dist y.mem ∧
            y.regs rk = (hkBfsLoop inst.graph inst.adj mate (fuel + 1) j dist frontier).k ∧
            y.regs rfound =
              (if (hkBfsLoop inst.graph inst.adj mate (fuel + 1) j dist frontier).found
                then 1 else 0) ∧
            (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
                a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) →
              y.mem a = x.mem a) := by
        have hc₃ : ¬(Cond.eq active one).Holds (x₂.set active 0) := by
          rw [Cond.holds_eq]
          wram_simp [hb₂.hone]
        have he_exit := ExecWithin.loop_exit (body := bfsLayerBody) (w := w) hc₃
        have hres : hkBfsLoop inst.graph inst.adj mate (fuel + 1) j dist frontier =
            ⟨s.dist, j, s.found⟩ := by
          dsimp only [hkBfsLoop]
          rw [← hs_def]
          rcases hstop with hsf | hse
          · simp [hsf]
          · cases s.found <;> simp [hse]
        refine ⟨x₂.set active 0,
          (ExecWithin.loop_iter hc (he_le.seq (he_front.seq he_tail)) he_exit).mono (by omega),
          fun i hi => by wram_simp [hr₂ i hi], by simpa only [hres, Data.set] using hdM₂,
          by wram_simp [hrk₂, hres], by wram_simp [hrf₂, hres], hf₂⟩
      by_cases hsf : s.found = true
      · have hrf_one : x₂.regs rfound = 1 := by simp [hrf₂, hsf]
        refine stop_of_tail ((WP.execWithin ?_ : ExecWithin _ _ _ _ 2).mono (by omega)) (Or.inl hsf)
        wram_exec [hrf_one, hb₂.hone, hb₂.hzero]
        rfl
      · have hrf_zero : x₂.regs rfound = 0 := by simp [hrf₂, hsf]
        by_cases hs_empty : s.next.isEmpty = true
        · have hs_nil : s.next = [] := List.isEmpty_iff.mp hs_empty
          have hqt_eq_le : x₂.regs qTail = le := by simp [hqt₂, hs_nil]
          refine stop_of_tail (WP.execWithin ?_) (Or.inr hs_empty)
          wram_exec [hrf_zero, hb₂.hone, hb₂.hzero, hqh₂, hqt_eq_le]
          rfl
        · have hs_nnil : s.next ≠ [] := fun h => hs_empty (by simp [h])
          have hqh_ne_qt : x₂.regs qHead ≠ x₂.regs qTail := by simpa [hqh₂, hqt₂] using hs_nnil
          have he_tail : ExecWithin w (ram[
              if rfound = one then [ active ← zero ] else [
                if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ] ] ] :
              Code .standard 34) x₂ (x₂.set rk (j + 1)) 5 :=
            WP.execWithin <| by
              wram_exec [hrf_zero, hb₂.hone, hrk₂, hqh_ne_qt]
              rfl
          have hb₃ : BaseRegs inst bOff (x₂.set rk (j + 1)) := hb₂.of_eq fun i hi => by wram_simp
          have hcsr₃ : CSRMem inst bOff (x₂.set rk (j + 1)).mem :=
            hcsr.of_outside fun a ha => hf₂ a (by omega)
          have hmate₃ : MateMem inst bOff mate (x₂.set rk (j + 1)).mem :=
            hmate.of_outside fun a ha => hf₂ a (by omega)
          obtain ⟨y, he_rec, hr₄, hdM₄, hrk₄, hrf₄, hf₄⟩ :=
            ih (j + 1) le s.dist s.next (x₂.set rk (j + 1)) hb₃ hcsr₃ hmate₃ hdM₂ hq_next₂
              (by wram_simp) (by wram_simp [hrf_zero]) (by wram_simp [hqh₂])
              (by wram_simp [hqt₂]) (by wram_simp [hact₂, hs_nnil])
              (by omega) (by dsimp only [le] at hbound₂; omega) (by omega)
          have hloop : hkBfsLoop inst.graph inst.adj mate (fuel + 1) j dist frontier =
              hkBfsLoop inst.graph inst.adj mate fuel (j + 1) s.dist s.next := by
            simp [hkBfsLoop, ← hs_def, hsf, hs_empty]
          rw [hloop]
          exact ⟨y, (ExecWithin.loop_iter hc (he_le.seq (he_front.seq he_tail)) he_rec).mono
              (by omega),
            fun i hi => (hr₄ i hi).trans (by wram_simp [hr₂ i hi]),
            hdM₄, hrk₄, hrf₄, fun a ha => (hf₄ a ha).trans (hf₂ a ha)⟩

/-- `O(m + r + |E|)` execution of `bfsCode`, agreeing with `hkBfs`. -/
theorem exec_bfsCode {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem inst bOff mate x.mem)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let b := hkBfs inst.graph inst.adj mate
    ∃ y, ExecWithin w bfsCode x y (51 * inst.m + 8 * inst.r + 36 * inst.numEdges + 33) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem inst bOff b.dist y.mem ∧
      y.regs rk = b.k ∧
      y.regs rfound = (if b.found then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  intro b
  obtain ⟨y₁, he₁, hr₁, hml₁, hf₁⟩ := exec_markMLCode x hb hmate hfit
  have hb₁ : BaseRegs inst bOff y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, hdM₂, hqM₂, hqh₂, hqt₂, hrk₂, hrf₂, hact₂, hnd₂, hiff₂, hf₂⟩ :=
    exec_seedBfsCode y₁ hb₁ hml₁ hfit
  set p := (List.finRange inst.m).foldl (hkBfsInitStep (hkMatchedLeft mate))
    (Vector.replicate inst.m none, [])
  have hb₂ : BaseRegs inst bOff y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hcsr₂ : CSRMem inst bOff y₂.mem :=
    hcsr.of_outside fun a ha => (hf₂ a (by omega)).trans (hf₁ a (by omega))
  have hmate₂ : MateMem inst bOff mate y₂.mem :=
    hmate.of_outside fun a ha => (hf₂ a (by omega)).trans (hf₁ a (by omega))
  have hcard_bound :
      p.2.length + (Finset.univ.filter fun w₀ => vget p.1 w₀ = none).card ≤ inst.m := by
    have hlen_eq : p.2.length = (Finset.univ.filter fun w₀ => ¬ vget p.1 w₀ = none).card := by
      rw [← List.toFinset_card_of_nodup hnd₂]
      congr 1
      ext w₀
      simp [← hiff₂ w₀]
    rw [hlen_eq, Nat.add_comm, Finset.card_filter_add_card_filter_not]
    simp
  obtain ⟨y₃, he₃, hr₃, hdM₃, hrk₃, hrf₃, hf₃⟩ :=
    exec_bfsLayersLoop (inst.m + 1) 0 0 p.1 p.2 y₂ hb₂ hcsr₂ hmate₂ hdM₂ hqM₂ hrk₂ hrf₂ hqh₂
      (by simpa using hqt₂) hact₂ (by omega) (by simpa using hcard_bound) (by omega) hfit
  have hinit_pot :
      vecPotential (fun x : Option ℕ => x = none) (bfsVertWeight inst) p.1 +
          (p.2.map (bfsVertWeight inst)).sum ≤
        vecPotential (fun x : Option ℕ => x = none) (bfsVertWeight inst)
            (Vector.replicate inst.m (none : Option ℕ)) +
          ((List.finRange inst.m).map (bfsVertWeight inst)).sum := by
    simpa [p] using bfsInit_potential (hkMatchedLeft mate) (bfsVertWeight inst)
      (List.finRange inst.m) (Vector.replicate inst.m (none : Option ℕ), [])
  have hrep_le := (vecPotential_le_sum (p := fun x : Option ℕ => x = none) (bfsVertWeight inst)
    (Vector.replicate inst.m (none : Option ℕ))).trans_eq (sum_bfsVertWeight inst)
  have hfin_sum : ((List.finRange inst.m).map (bfsVertWeight inst)).sum =
      18 * inst.numEdges + 11 * inst.m :=
    (Fin.sum_univ_def _).symm.trans (sum_bfsVertWeight inst)
  refine ⟨y₃, (he₁.seq (he₂.seq he₃)).mono ?_,
    fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (hr₁ i (by omega))),
    hdM₃, hrk₃, hrf₃,
    fun a ha => (hf₃ a (by omega)).trans ((hf₂ a (by omega)).trans (hf₁ a (by omega)))⟩
  omega

end Cslib.Algorithms.WordRAM.HopcroftKarp.Internal
