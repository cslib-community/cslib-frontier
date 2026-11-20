/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.LRAT.Steps
import Mathlib.Data.List.MinMax

/-!
# An LRAT checker on the word RAM: correctness and running time

This file proves the main theorem about the word-RAM LRAT checker
(`Cslib.Algorithms.WordRAM.LRAT.program`): on the input `encode φ cert` it halts with output `1`
exactly when `Cslib.Logic.PL.CNF.checkLRAT φ cert = true`, and otherwise with `0`, within
`60 L + 20 W + 20` instructions, where `L` is the length of the input and `W` is the total length
of the clauses that the hints of the certificate name (`Cslib.Algorithms.WordRAM.LRAT.certWork`).

## Main definitions

* `Cslib.Algorithms.WordRAM.LRAT.certWork`: the total length of the hinted clauses.

## Main results

* `Cslib.Algorithms.WordRAM.LRAT.program_spec`: correctness and the instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.LRAT

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Algorithms.WordRAM.ClauseCode Reg
open Std.Tactic.BVDecide (LRAT.IntAction)

/-! ### The database of the formula -/

/-- The numbered clauses of `ψ`, numbered from `j`. -/
def numbered (ψ : CNF ℕ) (j : ℕ) : List (ℕ × Clause ℕ) := (ψ.zipIdx j).map fun e => (e.2, e.1)

theorem numbered_append (ψ ψ' : CNF ℕ) (j : ℕ) :
    numbered (ψ ++ ψ') j = numbered ψ j ++ numbered ψ' (j + ψ.length) := by
  simp [numbered, List.zipIdx_append]

theorem numbered_singleton (c : Clause ℕ) (j : ℕ) : numbered [c] j = [(j, c)] := rfl

theorem fst_lt_of_mem_numbered {ψ : CNF ℕ} {j : ℕ} {e : ℕ × Clause ℕ} (he : e ∈ numbered ψ j) :
    e.1 < j + ψ.length := by
  induction ψ generalizing j with
  | nil => simp [numbered] at he
  | cons c ψ ih =>
    simp only [numbered, List.zipIdx_cons, List.map_cons, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · have := ih (j := j + 1) (by simpa [numbered] using he)
      simp only [List.length_cons]; omega

/-- The database `checkLRAT` starts from. -/
theorem zipIdx_map_eq_numbered (φ : CNF ℕ) :
    φ.zipIdx.map (fun e => (e.2 + 1, e.1)) = numbered φ 1 := by
  suffices ∀ n, (φ.zipIdx n).map (fun e => (e.2 + 1, e.1)) = numbered φ (n + 1) from this 0
  induction φ with
  | nil => simp [numbered]
  | cons c φ ih =>
    intro n
    simp only [List.zipIdx_cons, List.map_cons, numbered] at ih ⊢
    rw [ih (n + 1)]

theorem map_snd_numbered (ψ : CNF ℕ) (j : ℕ) : (numbered ψ j).map Prod.snd = ψ := by
  induction ψ generalizing j with
  | nil => rfl
  | cons c ψ ih => simpa [numbered, List.zipIdx_cons] using ih (j + 1)

theorem snd_mem_of_mem_numbered {ψ : CNF ℕ} {j : ℕ} {e : ℕ × Clause ℕ} (he : e ∈ numbered ψ j) :
    e.2 ∈ ψ := by
  rw [← map_snd_numbered ψ j]; exact List.mem_map_of_mem he

/-- Recording the address `a` of the encoding of `c` under a new number `i` appends `(i, c)` to
the database. -/
theorem TableAt.snoc {mem : ℕ → ℕ} {T : ℕ} {db : List (ℕ × Clause ℕ)} (h : TableAt mem T db)
    (i : ℕ) (c : Clause ℕ) (hi : db.find? (·.1 == i) = none) (a : ℕ) (ha : 0 < a)
    (haT : a + c.length + 1 ≤ T) (hc : HoldsList a (encodeClause c) mem) :
    TableAt (Function.update mem (tcell T i) a) T (db ++ [(i, c)]) := by
  have hfr : ∀ b, b < T → Function.update mem (tcell T i) a b = mem b := fun b hb =>
    Function.update_of_ne (by simp only [tcell]; omega) _ _
  intro j
  by_cases hj : i = j
  · subst hj
    refine ⟨fun hn => by simp [List.find?_append, hi] at hn, fun e he => ?_⟩
    simp only [List.find?_append, hi, Option.none_or, List.find?_cons, beq_self_eq_true,
      Option.some.injEq] at he
    subst he
    simp only [Function.update_self]
    refine ⟨ha, haT, hc.frame fun b _ hb => hfr b ?_⟩
    simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at hb
    omega
  · have hne : tcell T j ≠ tcell T i := by simp only [tcell]; omega
    have hfind : (db ++ [(i, c)]).find? (·.1 == j) = db.find? (·.1 == j) := by
      simp [List.find?_append, hj]
    rw [hfind, Function.update_of_ne hne]
    refine ⟨(h j).1, fun e he => ?_⟩
    obtain ⟨hpos, hlt, hl⟩ := (h j).2 e he
    refine ⟨hpos, hlt, hl.frame fun b _ hb => hfr b ?_⟩
    simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at hb
    omega

/-! ### Loading the formula -/

section Specs

variable {w : ℕ}

/-- **The loading loop** records the clauses `ψ` at `ptr` under the numbers that follow the
clauses `done` already recorded. -/
theorem loadLoop_spec (done ψ : CNF ℕ) (x : Data 28) (M T : ℕ)
    (hone : x.regs one = 1) (hT : x.regs tbase = T) (hn : x.regs nCl = done.length + ψ.length)
    (hcnt : x.regs cnt = done.length) (hid : x.regs Reg.id = done.length + 1)
    (hl : HoldsList (x.regs ptr) (ψ.flatMap encodeClause) x.mem)
    (hpT : x.regs ptr + (ψ.flatMap encodeClause).length ≤ T) (hp1 : 1 ≤ x.regs ptr)
    (htab : TableAt x.mem T (numbered done 1)) (hfr : Fresh x.mem T 1)
    (hnM : done.length + ψ.length + 1 ≤ M) (hw : Fits w (T + 2 * M + 2)) :
    ∃ y, ExecWithin w loadLoop x y (10 * ψ.length + 2) ∧
      y.regs ptr = x.regs ptr + (ψ.flatMap encodeClause).length ∧
      TableAt y.mem T (numbered (done ++ ψ) 1) ∧ Fresh y.mem T 1 ∧
      ∀ a < T, y.mem a = x.mem a := by
  induction ψ generalizing done x with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simp, by simpa using htab, hfr,
      fun _ _ => rfl⟩
    simp [Cond.holds_lt, hn, hcnt]
  | cons c ψ ih =>
    simp only [List.length_cons] at hn hnM
    simp only [List.flatMap_cons, List.length_append, encodeClause, encodeClauseBy,
      List.length_cons, List.length_map] at hpT
    have hc : (Cond.lt cnt nCl).Holds x := by simp only [Cond.holds_lt, hn, hcnt]; omega
    rw [List.flatMap_cons] at hl
    obtain ⟨hcl, hrest⟩ := holdsList_append_iff.mp hl
    obtain ⟨hlen, -⟩ := holdsList_cons_iff.mp hcl
    simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at hrest
    have : Fits w (done.length + 1 + (done.length + 1)) := hw.of_le (by omega)
    have : Fits w (T + (done.length + 1 + (done.length + 1))) := hw.of_le (by omega)
    have : Fits w (x.regs ptr + 1) := hw.of_le (by omega)
    have : Fits w (x.regs ptr + 1 + c.length) := hw.of_le (by omega)
    have : Fits w (done.length + 1 + 1) := hw.of_le (by omega)
    have : Fits w (done.length + 1) := hw.of_le (by omega)
    have hnone : (numbered done 1).find? (·.1 == done.length + 1) = none := by
      rw [List.find?_eq_none]
      intro e he
      have := fst_lt_of_mem_numbered he
      simp only [beq_iff_eq]; omega
    have htab' := htab.snoc (done.length + 1) c hnone (x.regs ptr) (by omega) (by omega) hcl
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold loadBody
    wram_exec [hid, hT, hone, hlen, hcnt]
    refine WP.name fun x' hx' => ?_
    obtain ⟨z, hz, hzp, hztab, hzfr, hzm⟩ :=
      ih (done ++ [c]) x' (by subst hx'; wram_simp [hone]) (by subst hx'; wram_simp [hT])
        (by subst hx'; wram_simp [hn]; simp; omega) (by subst hx'; wram_simp; simp)
        (by subst hx'; wram_simp; simp)
        (by
          subst hx'; wram_simp
          have := hrest.frame
            (mem' := Function.update x.mem (T + (done.length + 1 + (done.length + 1))) (x.regs ptr))
            fun a _ ha => by apply Function.update_of_ne; omega
          simpa [Nat.add_assoc, Nat.add_comm] using this)
        (by subst hx'; wram_simp; omega) (by subst hx'; wram_simp; omega)
        (by
          subst hx'; wram_simp
          rw [numbered_append, numbered_singleton]
          simpa [Nat.add_comm] using htab')
        (by subst hx'; wram_simp; exact hfr.of_tcell _ _) (by simp; omega)
    subst hx'
    refine WP.of_execWithin hz ?_
    wram_simp at hzp hzm
    refine ⟨?_, ?_, by simpa using hztab, hzfr, fun a ha => ?_⟩
    · simp only [List.length_cons]; omega
    · rw [hzp]; simp [encodeClause, encodeClauseBy]; omega
    · rw [hzm a ha]; exact Function.update_of_ne (by omega) _ _

end Specs

/-! ### The checker -/

/-- The total length of the clauses that the hints of `cert` name, in the database of each
step. -/
def certWork (φ : CNF ℕ) (cert : Array LRAT.IntAction) : ℕ :=
  stepsWork (φ.zipIdx.map fun e => (e.2 + 1, e.1)) cert.toList

/-- The word size the checker needs on the input `encode φ cert`: the input's addresses, and
twice its largest word, fit. -/
def wordBound (φ : CNF ℕ) (cert : Array LRAT.IntAction) : ℕ :=
  (encode φ cert).length + 2 * (encode φ cert).foldr max 0 + 5

theorem length_le_length_flatMap_encodeClause (ψ : CNF ℕ) :
    ψ.length ≤ (ψ.flatMap encodeClause).length := by
  induction ψ with
  | nil => simp
  | cons c ψ ih => simp [encodeClause, encodeClauseBy]; omega

section Specs

variable {w : ℕ}

/-- **The LRAT checker** leaves `checkLRAT φ cert` in `out`, within
`60 L + 20 W + 20` instructions on an input of length `L` whose hinted clauses have total length
`W`. -/
theorem checker_spec (φ : CNF ℕ) (cert : Array LRAT.IntAction)
    (hw : Fits w (wordBound φ cert)) :
    ∃ y, ExecWithin w checker (Data.init (encode φ cert)) y
        (60 * (encode φ cert).length + 20 * certWork φ cert + 20) ∧
      y.regs out = (CNF.checkLRAT φ cert).toNat := by
  set input := encode φ cert with hinput
  set L := input.length
  set T := L + 1
  set M := input.foldr max 0 + 1
  have hTL : T = L + 1 := rfl
  have hM : ∀ v ∈ input, v + 1 ≤ M := fun v hv => by have := List.le_max_of_le' 0 hv le_rfl; omega
  have hw' : Fits w (T + 2 * M + 2) := hw.of_le (by simp only [wordBound, T, M, L, hinput]; omega)
  set F := φ.flatMap encodeClause
  set C := cert.toList.flatMap encodeAction
  have hinputeq : input = φ.length :: (F ++ C) := rfl
  have hL : L = 1 + F.length + C.length := by simp [L, hinputeq]; omega
  have hmem : ∀ a, (Data.init input : Data 28).mem a =
      if a = 0 then L else input.getD (a - 1) 0 := fun _ => rfl
  have hzeroT : ∀ a, T ≤ a → (Data.init input : Data 28).mem a = 0 := fun a ha => by
    rw [hmem, ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [T, L] at ha; omega)]
    rfl
  have hFC : HoldsList 2 (F ++ C) (Data.init input : Data 28).mem := fun i => by
    change (Data.init input : Data 28).mem (2 + i.val) = (F ++ C)[i.val]
    rw [show 2 + i.val = (1 + i.val) + 1 by omega, Data.init_mem_succ]
    simp only [hinputeq, Nat.add_comm 1 i.val, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using i.isLt)]
    rfl
  obtain ⟨hF, hC⟩ := holdsList_append_iff.mp hFC
  have hm1 : (Data.init input : Data 28).mem 1 = φ.length := by
    rw [Data.init_mem_succ]; simp [hinputeq]
  have hφM : φ.length + 1 ≤ M := hM _ (by simp [hinputeq])
  have : Fits w 1 := hw'.of_le (by omega)
  have : Fits w 2 := hw'.of_le (by omega)
  have : Fits w 3 := hw'.of_le (by omega)
  have : Fits w L := hw'.of_le (by omega)
  have : Fits w (L + 1) := hw'.of_le (by omega)
  have : Fits w φ.length := hw'.of_le (by omega)
  have : Fits w (1 + 1) := hw'.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold checker setup
  wram_exec [Data.init_regs, Data.init_mem_zero, hm1]
  refine WP.name fun x' hx' => ?_
  have hld := loadLoop_spec (w := w) [] φ x' M T
    (by subst hx'; wram_simp) (by subst hx'; wram_simp; rfl) (by subst hx'; wram_simp; simp)
    (by subst hx'; wram_simp; rfl) (by subst hx'; wram_simp; rfl)
    (by subst hx'; wram_simp; exact hF)
    (by
      subst hx'; wram_simp
      have : (φ.flatMap encodeClause).length = F.length := rfl
      omega)
    (by subst hx'; wram_simp)
    (by
      subst hx'; wram_simp
      refine fun i => ⟨fun _ => hzeroT _ (by simp only [tcell]; omega), fun e he => ?_⟩
      simp [numbered] at he)
    (by subst hx'; wram_simp; exact fun c => by rw [hzeroT _ (by simp only [acell]; omega)]; omega)
    (by simpa using hφM) hw'
  subst hx'
  obtain ⟨y, hy, ⟨hyp, hytab, hyfr, hym⟩, hpres⟩ := exists_execWithin_preserves hld
  refine WP.of_execWithin hy ?_
  have hy0 := hpres zero (by decide)
  have hy1 := hpres one (by decide)
  have hy3 := hpres three (by decide)
  have hyE := hpres endp (by decide)
  have hyT := hpres tbase (by decide)
  have hys := hpres stamp (by decide)
  have hyo := hpres out (by decide)
  wram_simp [Data.init_regs] at hyp hym hy0 hy1 hy3 hyE hyT hys hyo
  simp only [List.nil_append] at hytab
  have hFl : (List.flatMap encodeClause φ).length = F.length := rfl
  have hLl : input.length = L := rfl
  rw [hFl] at hyp
  rw [hLl] at hyE hyT
  have hSW : (stepWords cert.toList).length = C.length := rfl
  have hdb : φ.zipIdx.map (fun e => (e.2 + 1, e.1)) = numbered φ 1 := zipIdx_map_eq_numbered φ
  have hst := (stepLoop_spec (w := w) cert.toList (numbered φ 1) y M T 1
    ⟨hy0, hy1, hy3, hyE, hyT, hys, hyo, hytab, hyfr,
      fun e he l hl => hM _ (by
        rw [hinputeq]
        refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨e.2, snd_mem_of_mem_numbered he, ?_⟩))
        exact List.mem_cons_of_mem _ (List.mem_map_of_mem hl)),
      hw', by rw [hyp]; omega⟩
    (by
      rw [hyp]
      exact hC.frame fun a _ ha => hym a (by omega))
    (by rw [hyp]; omega)
    (fun v hv => hM v (by
      rw [hinputeq]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hv))))
  obtain ⟨z, hz, hzo⟩ := hst
  refine WP.of_execWithin hz ?_
  refine ⟨?_, ?_⟩
  · have := length_le_length_flatMap_encodeClause φ
    simp only [certWork, hdb]
    omega
  · rw [hzo, CNF.checkLRAT, hdb]

end Specs

/-- **The LRAT checker on the word RAM.** At any word size `w` that fits `wordBound φ cert`, the
program run on the input `encode φ cert` of length `L` halts with output `1` when
`checkLRAT φ cert = true` and `0` otherwise, after at most `60 L + 20 W + 21` instructions, where
`W = certWork φ cert` is the total length of the clauses that the hints of `cert` name. -/
theorem program_spec (φ : CNF ℕ) (cert : Array LRAT.IntAction) {w : ℕ}
    (hw : Fits w (wordBound φ cert)) :
    ∃ n ≤ 60 * (encode φ cert).length + 20 * certWork φ cert + 21,
      Executes w program (State.init (encode φ cert)) (CNF.checkLRAT φ cert).toNat n := by
  obtain ⟨y, ⟨n, hn, he⟩, hy⟩ := checker_spec φ cert hw
  exact ⟨n + 1, by omega, hy ▸ he.executes out⟩

end Cslib.Algorithms.WordRAM.LRAT

end
