/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
public import CslibFrontier.Algorithms.WordRAM.LRAT.Propagate

/-!
# An LRAT checker on the word RAM: the steps of a certificate

This file proves that the step loop of the word-RAM LRAT checker
(`Cslib.Algorithms.WordRAM.LRAT.stepLoop`) computes `Cslib.Logic.PL.CNF.checkLRATAux`.

## Main definitions

* `Cslib.Algorithms.WordRAM.LRAT.stepsWork`: the total length of the clauses that the hints of
  the steps name, in the database of each step.

## Main results

* `Cslib.Algorithms.WordRAM.LRAT.stepLoop_spec`: the step loop leaves
  `checkLRATAux db cert` in `out`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.LRAT

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Algorithms.WordRAM.ClauseCode Reg
open Std.Tactic.BVDecide (LRAT.IntAction)

/-! ### The database under additions and deletions -/

theorem find?_filter_of_imp {α : Type*} {p q : α → Bool} (l : List α) (h : ∀ a, p a → q a) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a l ih => cases hq : q a <;> cases hp : p a <;> simp_all

/-- Recording the address `a` of the encoding of `c` under number `i` adds `(i, c)` to the
database. -/
theorem TableAt.cons {mem : ℕ → ℕ} {T : ℕ} {db : List (ℕ × Clause ℕ)} (h : TableAt mem T db)
    (i : ℕ) (c : Clause ℕ) (a : ℕ) (ha : 0 < a) (haT : a + c.length + 1 ≤ T)
    (hc : HoldsList a (encodeClause c) mem) :
    TableAt (Function.update mem (tcell T i) a) T ((i, c) :: db) := by
  have hfr : ∀ b, b < T → Function.update mem (tcell T i) a b = mem b := fun b hb =>
    Function.update_of_ne (by simp only [tcell]; omega) _ _
  intro j
  by_cases hj : i = j
  · subst hj
    refine ⟨fun hn => by simp at hn, fun e he => ?_⟩
    simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq] at he
    subst he
    simp only [Function.update_self]
    refine ⟨ha, haT, hc.frame fun b _ hb => hfr b ?_⟩
    simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at hb; omega
  · have hfind : ((i, c) :: db).find? (·.1 == j) = db.find? (·.1 == j) := by simp [hj]
    rw [hfind, Function.update_of_ne (by simp only [tcell]; omega)]
    refine ⟨(h j).1, fun e he => ?_⟩
    obtain ⟨hpos, hlt, hl⟩ := (h j).2 e he
    refine ⟨hpos, hlt, hl.frame fun b _ hb => hfr b ?_⟩
    simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at hb; omega

/-- Clearing the cell of number `i` deletes the clauses numbered `i`. -/
theorem TableAt.erase {mem : ℕ → ℕ} {T : ℕ} {db : List (ℕ × Clause ℕ)} (h : TableAt mem T db)
    (i : ℕ) :
    TableAt (Function.update mem (tcell T i) 0) T (db.filter fun e => !(e.1 == i)) := by
  have hfr : ∀ b, b < T → Function.update mem (tcell T i) 0 b = mem b := fun b hb =>
    Function.update_of_ne (by simp only [tcell]; omega) _ _
  intro j
  by_cases hj : i = j
  · subst hj
    have hnone : (db.filter fun e => !(e.1 == i)).find? (·.1 == i) = none :=
      List.find?_eq_none.mpr fun e he => by simpa using (List.mem_filter.mp he).2
    simp [hnone]
  · have hfind : (db.filter fun e => !(e.1 == i)).find? (·.1 == j) = db.find? (·.1 == j) :=
      find?_filter_of_imp db fun e he => by simpa [beq_iff_eq.mp he] using Ne.symm hj
    rw [hfind, Function.update_of_ne (by simp only [tcell]; omega)]
    refine ⟨(h j).1, fun e he => ?_⟩
    obtain ⟨hpos, hlt, hl⟩ := (h j).2 e he
    refine ⟨hpos, hlt, hl.frame fun b _ hb => hfr b ?_⟩
    simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at hb; omega

/-! ### The trail -/

/-- Every assignment cell holds less than the stamp `s`: the trail of a new step is empty. -/
def Fresh (mem : ℕ → ℕ) (T s : ℕ) : Prop := ∀ c, mem (acell T c) < s

theorem Fresh.trailAt {mem : ℕ → ℕ} {T s : ℕ} (h : Fresh mem T s) : TrailAt mem T s [] :=
  fun l => ⟨by simpa using (h (litCode l)).ne, (h (litCode l)).le⟩

theorem TrailAt.fresh_succ {mem : ℕ → ℕ} {T s : ℕ} {trail : List (Literal ℕ)}
    (h : TrailAt mem T s trail) : Fresh mem T (s + 1) := by
  intro c
  obtain ⟨l, rfl⟩ : ∃ l, litCode l = c :=
    ⟨(c / 2, c % 2 == 1), by
      simp only [litCode, litCodeBy]
      rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h] <;> omega⟩
  exact Nat.lt_succ_of_le (h l).2

theorem TrailAt.congr {mem : ℕ → ℕ} {T s : ℕ} {t₁ t₂ : List (Literal ℕ)}
    (h : TrailAt mem T s t₁) (ht : ∀ l, l ∈ t₁ ↔ l ∈ t₂) : TrailAt mem T s t₂ :=
  fun l => ⟨(h l).1.trans (ht l), (h l).2⟩

theorem Fresh.of_tcell {mem : ℕ → ℕ} {T s : ℕ} (h : Fresh mem T s) (i v : ℕ) :
    Fresh (Function.update mem (tcell T i) v) T s := fun c => by
  rw [Function.update_of_ne (by simp only [tcell, acell]; omega)]
  exact h c

theorem TrailAt.of_tcell {mem : ℕ → ℕ} {T s : ℕ} {t : List (Literal ℕ)} (h : TrailAt mem T s t)
    (i v : ℕ) : TrailAt (Function.update mem (tcell T i) v) T s t := fun l => by
  rw [Function.update_of_ne (by simp only [tcell, acell]; omega)]
  exact h l

/-! ### Work -/

/-- The total length of the clauses the hints of the steps name, in the database of each step,
following `checkLRATAux` as if every step were accepted. -/
def stepsWork : List (ℕ × Clause ℕ) → List LRAT.IntAction → ℕ
  | _, [] => 0
  | db, .addEmpty _ hints :: _ => hintsWork db hints.toList
  | db, .addRup i c hints :: rest =>
    hintsWork db hints.toList + stepsWork ((i, Clause.ofDIMACS c.toList) :: db) rest
  | _, .addRat .. :: _ => 0
  | db, .del ids :: rest => stepsWork (db.filter fun e => !ids.toList.contains e.1) rest

/-! ### Assuming the negated clause -/

section Specs

variable {w : ℕ}

/-- **Assuming the negated clause**: the loop over the literals `ls` at `lptr` puts their
negations on the trail, changing only assignment cells. -/
theorem assumeLoop_spec (ls : List (Literal ℕ)) (trail : List (Literal ℕ)) (x : Data 28)
    (M T s : ℕ) (hone : x.regs one = 1) (hT : x.regs tbase = T) (hst : x.regs stamp = s)
    (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hle : x.regs lend = x.regs lptr + ls.length) (hlT : x.regs lend ≤ T)
    (htr : TrailAt x.mem T s trail)
    (hM : ∀ l ∈ ls, litCode l + 1 ≤ M) (hw : Fits w (T + 2 * M + 2)) :
    ∃ y, ExecWithin w assumeLoop x y (10 * ls.length + 2) ∧ y.regs lptr = x.regs lend ∧
      OnlyAsg T x.mem y.mem ∧
      TrailAt y.mem T s (ls.reverse.map Std.Sat.Literal.negate ++ trail) ∧
      y.regs one = 1 ∧ y.regs tbase = T ∧ y.regs stamp = s ∧ y.regs lend = x.regs lend := by
  induction ls generalizing x trail with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simp [hle], OnlyAsg.refl _ _,
      by simpa using htr, hone, hT, hst, rfl⟩
    simp [Cond.holds_lt, hle]
  | cons l ls ih =>
    simp only [List.length_cons] at hle
    have hc : (Cond.lt lptr lend).Holds x := by simp only [Cond.holds_lt, hle]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp (by simpa using hl)
    have hMl := hM l (by simp)
    have hx1 : litCode (Std.Sat.Literal.negate l) ≤ litCode l + 1 := litCodeBy_negate_le _root_.id l
    have : Fits w (litCode l) := hw.of_le (by omega)
    have : Fits w (litCode (Std.Sat.Literal.negate l)) := hw.of_le (by omega)
    have : Fits w (litCode (Std.Sat.Literal.negate l) + litCode (Std.Sat.Literal.negate l)) :=
      hw.of_le (by omega)
    have : Fits w (litCode (Std.Sat.Literal.negate l) + litCode (Std.Sat.Literal.negate l) + 1) :=
      hw.of_le (by omega)
    have : Fits w (T + (litCode (Std.Sat.Literal.negate l) +
        litCode (Std.Sat.Literal.negate l) + 1)) := hw.of_le (by omega)
    have hOA : OnlyAsg T x.mem
        (Function.update x.mem (acell T (litCode (Std.Sat.Literal.negate l))) s) :=
      OnlyAsg.update T _ s x.mem
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold assumeBody
    wram_exec [hlit, hone, litCodeBy_xor_one, hT, hst]
    wram_call (ih (Std.Sat.Literal.negate l :: trail) _)
      [hone, hT, hst, hle, htr.update _] with z ⟨hzp, hzoa, hztr, hz1, hzT, hzs, hze⟩
    · wram_simp at hzp hzoa hze
      exact ⟨by simp only [List.length_cons]; omega, by rw [hzp], hOA.trans hzoa,
        by simpa using hztr, hz1, hzT, hzs, hze⟩
    · wram_simp
      exact hrest.frame fun a _ ha => hOA.eq_of_lt (by simp only [List.length_map] at ha; omega)
    · exact fun l' hl' => hM l' (by simp [hl'])

/-- **A RUP step** on the words `i :: encodeClause c ++ encodeNums hints` at `ptr`: when
propagation from the negated clause along the hints succeeds, it adds `(i, c)` to the database,
advances the stamp, and leaves `ptr` past the step; otherwise it rejects. -/
theorem rupStep_spec (db : List (ℕ × Clause ℕ)) (i : ℕ) (c : Clause ℕ) (hints : List ℕ)
    (x : Data 28) (M T s : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (hE : x.regs endp = T)
    (hT : x.regs tbase = T) (hst : x.regs stamp = s)
    (hl : HoldsList (x.regs ptr) (i :: encodeClause c ++ encodeNums hints) x.mem)
    (hpT : x.regs ptr + (i :: encodeClause c ++ encodeNums hints).length ≤ T)
    (htab : TableAt x.mem T db) (hfr : Fresh x.mem T s)
    (hiM : i ≤ M) (hcM : ∀ l ∈ c, litCode l + 1 ≤ M) (hhM : ∀ h ∈ hints, h ≤ M)
    (hdbM : ∀ e ∈ db, ∀ l ∈ e.2, litCode l + 1 ≤ M)
    (hw : Fits w (T + 2 * M + 2)) (hsT : s + 1 ≤ T) :
    ∃ y, ExecWithin w rupStep x y
        (10 * c.length + 40 * hints.length + 20 * hintsWork db hints + 30) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs endp = T ∧ y.regs tbase = T ∧
      if CNF.propagateHints db (c.map Std.Sat.Literal.negate) hints then
        y.regs ptr = x.regs ptr + (i :: encodeClause c ++ encodeNums hints).length ∧
        y.regs stamp = s + 1 ∧ y.regs out = x.regs out ∧
        TableAt y.mem T ((i, c) :: db) ∧ Fresh y.mem T (s + 1) ∧ ∀ a < T, y.mem a = x.mem a
      else y.regs out = 0 ∧ y.regs ptr = T := by
  simp only [List.cons_append, List.length_cons, List.length_append, encodeClause, encodeClauseBy,
    encodeNums, List.length_map] at hl hpT
  obtain ⟨hli, hl⟩ := holdsList_cons_iff.mp hl
  obtain ⟨hlen, hl⟩ := holdsList_cons_iff.mp hl
  obtain ⟨hlits, hl⟩ := holdsList_append_iff.mp hl
  simp only [List.length_map] at hl
  refine WP.exists_execWithin ?_
  unfold rupStep
  wram_exec [hli, hone, hlen]
  wram_call (assumeLoop_spec (w := w) c [] _ M T s) [hone, hT, hst, hlits, hfr.trailAt, hcM, hw]
    with y ⟨hyp, hyoa, hytr, hy1, hyT, hys, hye⟩
  wram_simp at hyp hyoa hye
  have htr' : TrailAt y.mem T s (c.map Std.Sat.Literal.negate) :=
    hytr.congr fun l => by simp
  wram_exec [hyp, hye]
  have hlh : HoldsList (x.regs ptr + 1 + 1 + c.length) (encodeNums hints) y.mem := by
    have := hl.frame (mem' := y.mem) fun a _ ha => hyoa.eq_of_lt (by
      simp only [List.length_cons] at ha; omega)
    simpa [encodeNums, Nat.add_assoc] using this
  have hy0 : y.regs zero = 0 := by regs_frame
  wram_call (propagate_spec (w := w) db hints (c.map Std.Sat.Literal.negate) _ M T s)
    [hy0, hy1, hyT, hys, hlh, htab.of_onlyAsg hyoa, htr', hhM, hdbM, hw]
    with z ⟨hzres, hzp, hzoa, ⟨tr, hztr⟩, hz0, hz1, hzT, hzs⟩
  wram_simp at hzp hzoa
  cases hpr : CNF.propagateHints db (c.map Std.Sat.Literal.negate) hints
  · rw [hpr] at hzres
    have hre : z.regs res = z.regs zero := by rw [hzres, hz0]; rfl
    unfold reject
    wram_exec [hre]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wram_simp
    exact ⟨hz0, hz1, by regs_frame, hzT, by regs_frame⟩
  · rw [hpr] at hzres
    have hzres' : z.regs res ≠ z.regs zero := by rw [hzres, hz0]; decide
    have hzid : z.regs Reg.id = i := by regs_frame
    have hzc : z.regs caddr = x.regs ptr + 1 := by regs_frame
    wram_exec * [hzres', hzid, hzc]
    simp only [↓reduceIte]
    wram_simp
    have hOA := hyoa.trans hzoa
    have hcz : HoldsList (x.regs ptr + 1) (encodeClause c) z.mem :=
      (holdsList_cons_iff.mpr ⟨hlen, hlits⟩).frame fun a _ ha => hOA.eq_of_lt (by
        simp only [List.length_cons, List.length_map] at ha; omega)
    refine ⟨hz0, hz1, by regs_frame, hzT, ?_, by regs_frame, ?_, ?_, fun a ha => ?_⟩
    · rw [hzp]; simp [encodeClause, encodeClauseBy, encodeNums]; omega
    · exact (htab.of_onlyAsg hOA).cons i c _ (by omega) (by omega) hcz
    · exact hztr.fresh_succ.of_tcell i _
    · have := hOA.eq_of_lt ha; mem_frame

theorem filter_contains_cons (db : List (ℕ × Clause ℕ)) (h : ℕ) (hs : List ℕ) :
    (db.filter fun e => !(e.1 == h)).filter (fun e => !hs.contains e.1) =
      db.filter fun e => !(h :: hs).contains e.1 := by
  rw [List.filter_filter]
  exact congrArg db.filter (funext fun e => by
    simp only [List.contains_cons, Bool.not_or, Bool.and_comm])

/-- **The deletion loop** clears the table cells of the numbers in `[ptr, hend)`. -/
theorem delLoop_spec (db : List (ℕ × Clause ℕ)) (ids : List ℕ) (x : Data 28) (M T s : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (hT : x.regs tbase = T)
    (hl : HoldsList (x.regs ptr) ids x.mem) (hhe : x.regs hend = x.regs ptr + ids.length)
    (hhT : x.regs hend ≤ T)
    (htab : TableAt x.mem T db) (hfr : Fresh x.mem T s)
    (hM : ∀ i ∈ ids, i ≤ M) (hw : Fits w (T + 2 * M + 2)) :
    ∃ y, ExecWithin w (.loop (.lt ptr hend) delBody) x y (8 * ids.length + 2) ∧
      y.regs ptr = x.regs hend ∧
      TableAt y.mem T (db.filter fun e => !ids.contains e.1) ∧ Fresh y.mem T s ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = T ∧ ∀ a < T, y.mem a = x.mem a := by
  induction ids generalizing x db with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simp [hhe], by simpa using htab, hfr,
      hzero, hone, hT, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hhe]
  | cons h ids ih =>
    simp only [List.length_cons] at hhe
    have hc : (Cond.lt ptr hend).Holds x := by simp only [Cond.holds_lt, hhe]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp hl
    have hhM := hM h (by simp)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold delBody
    wram_exec [hlit, hT, hzero, hone]
    wram_call (ih (db.filter fun e => !(e.1 == h)) _)
      [hzero, hone, hT, hhe, htab.erase h, hfr.of_tcell h 0]
      with z ⟨hzp, hztab, hzfr, hz0, hz1, hzT, hzm⟩
    · wram_simp at hzp hzm
      refine ⟨by simp only [List.length_cons]; omega, hzp, ?_, hzfr, hz0, hz1, hzT, by mem_frame⟩
      rw [← filter_contains_cons]; exact hztab
    · wram_simp
      exact hrest.frame fun a _ ha => Function.update_of_ne (by omega) _ _
    · exact fun i hi => hM i (by simp [hi])

/-- **A deletion step** on the words `encodeNums ids` at `ptr`. -/
theorem delStep_spec (db : List (ℕ × Clause ℕ)) (ids : List ℕ) (x : Data 28) (M T s : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (hT : x.regs tbase = T)
    (hl : HoldsList (x.regs ptr) (encodeNums ids) x.mem)
    (hpT : x.regs ptr + 1 + ids.length ≤ T)
    (htab : TableAt x.mem T db) (hfr : Fresh x.mem T s)
    (hM : ∀ i ∈ ids, i ≤ M) (hw : Fits w (T + 2 * M + 2)) :
    ∃ y, ExecWithin w delStep x y (8 * ids.length + 6) ∧
      y.regs ptr = x.regs ptr + 1 + ids.length ∧
      TableAt y.mem T (db.filter fun e => !ids.contains e.1) ∧ Fresh y.mem T s ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = T ∧ ∀ a < T, y.mem a = x.mem a := by
  obtain ⟨hlen, hrest⟩ := holdsList_cons_iff.mp hl
  refine WP.exists_execWithin ?_
  unfold delStep
  wram_exec [hlen, hone]
  wram_call (delLoop_spec (w := w) db ids _ M T s) [hzero, hone, hT, hrest, htab, hfr, hM, hw]
    with y ⟨hyp, hytab, hyfr, hy0, hy1, hyT, hym⟩
  wram_simp at hyp hym
  exact ⟨by omega, hyp, hytab, hyfr, hy0, hy1, hyT, hym⟩

/-- The registers and memory of the step loop before a step, with the database `db` and the
stamp `s`. -/
structure StepInv (w M T s : ℕ) (db : List (ℕ × Clause ℕ)) (x : Data 28) : Prop where
  /-- Register `zero` holds `0`. -/
  zero : x.regs zero = 0
  /-- Register `one` holds `1`. -/
  one : x.regs one = 1
  /-- Register `three` holds `3`. -/
  three : x.regs three = 3
  /-- The input ends just before `T`. -/
  endp : x.regs endp = T
  /-- The table and the assignment start at `T`. -/
  tbase : x.regs tbase = T
  /-- The stamp of the next step. -/
  stamp : x.regs stamp = s
  /-- No answer yet. -/
  out : x.regs out = 0
  /-- The table represents `db`. -/
  table : TableAt x.mem T db
  /-- The trail of the next step is empty. -/
  fresh : Fresh x.mem T s
  /-- The literal codes of the database are below `M`. -/
  dbM : ∀ e ∈ db, ∀ l ∈ e.2, litCode l + 1 ≤ M
  /-- Every address and value the checker computes fits a word. -/
  fits : Fits w (T + 2 * M + 2)
  /-- The stamp is at most the cursor, so it stays below `T`. -/
  stamp_le : s ≤ x.regs ptr

/-- The words of a list of steps. -/
abbrev stepWords (rest : List LRAT.IntAction) : List ℕ := rest.flatMap encodeAction

/-- **The step loop** computes `checkLRATAux db rest` for the steps `rest` at `ptr`, which run to
the end of the input. -/
theorem stepLoop_spec (rest : List LRAT.IntAction) (db : List (ℕ × Clause ℕ)) (x : Data 28)
    (M T s : ℕ) (hinv : StepInv w M T s db x)
    (hl : HoldsList (x.regs ptr) (stepWords rest) x.mem)
    (hpT : x.regs ptr + (stepWords rest).length = T)
    (hM : ∀ v ∈ stepWords rest, v + 1 ≤ M) :
    ∃ y, ExecWithin w stepLoop x y (60 * (stepWords rest).length + 20 * stepsWork db rest + 2) ∧
      y.regs out = (CNF.checkLRATAux db rest).toNat := by
  induction rest generalizing db s x with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simp [hinv.out, CNF.checkLRATAux]⟩
    simp only [stepWords, List.flatMap_nil, List.length_nil, Nat.add_zero] at hpT
    simp [Cond.holds_lt, hpT, hinv.endp]
  | cons a rest ih =>
    rw [stepWords, List.flatMap_cons, ← stepWords] at hl hpT hM
    simp only [List.length_append] at hpT
    obtain ⟨hla, hlr⟩ := holdsList_append_iff.mp hl
    have hpos : 0 < (encodeAction a).length := by cases a <;> simp [encodeAction]
    have hc : (Cond.lt ptr endp).Holds x := by simp only [Cond.holds_lt, hinv.endp]; omega
    have hw := hinv.fits
    have hMa : ∀ v ∈ encodeAction a, v + 1 ≤ M := fun v hv => hM v (List.mem_append_left _ hv)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold stepBody
    cases a with
    | addEmpty i hints =>
      simp only [encodeAction] at hla hMa hpT
      obtain ⟨htag, hla⟩ := holdsList_cons_iff.mp hla
      wram_exec [htag, hinv.zero, hinv.one]
      unfold emptyStep
      wram_call (propagate_spec (w := w) db hints.toList [] _ M T s)
        [hinv.zero, hinv.one, hinv.tbase, hinv.stamp, hla, hinv.table, hinv.fresh.trailAt,
          hinv.dbM, hw]
        with y ⟨hyres, -, -, -, -, -, -, -⟩
      · have hyE : y.regs endp = T := by regs_frame
        wram_exec [hyE]
        refine WP.loop_exit (by wram_simp [Cond.holds_lt, hyE]) ?_
        wram_simp
        exact ⟨by simp [stepsWork, encodeAction, encodeNums]; omega, by rw [hyres]; rfl⟩
      · wram_simp; simp [encodeAction, encodeNums] at hpT ⊢; omega
      · intro h hh; have := hMa h (by simp [encodeNums, hh]); omega
    | addRup i c hints =>
      set c' := Clause.ofDIMACS c.toList with hc'
      have hea : (encodeAction (.addRup i c hints)).length = c'.length + hints.size + 4 := by
        simp [encodeAction, encodeClause, encodeClauseBy, encodeNums, c']; omega
      have hwl : (i :: encodeClause c' ++ encodeNums hints.toList).length =
          c'.length + hints.size + 3 := by
        simp [encodeClause, encodeClauseBy, encodeNums]; omega
      rw [hea] at hpT
      simp only [stepWords] at hpT
      simp only [encodeAction] at hla hMa
      obtain ⟨htag, hla⟩ := holdsList_cons_iff.mp hla
      have hcl : ∀ l ∈ c', litCode l + 1 ≤ M := fun l hl =>
        hMa _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_map_of_mem hl)))))
      have hiM : i + 1 ≤ M :=
        hMa i (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hhM : ∀ h ∈ hints.toList, h + 1 ≤ M := fun h hh =>
        hMa h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
      wram_exec [htag, hinv.zero, hinv.one]
      wram_call (rupStep_spec (w := w) db i c' hints.toList _ M T s)
        [hinv.zero, hinv.one, hinv.endp, hinv.tbase, hinv.stamp, hla, hinv.table, hinv.fresh,
          hinv.dbM, hw, hcl]
        with y ⟨hy0, hy1, hyE, hyT, hyif⟩
      · wram_simp at hyif
        cases hpr : CNF.propagateHints db (c'.map Std.Sat.Literal.negate) hints.toList
        · simp only [hpr, Bool.false_eq_true, ↓reduceIte] at hyif
          obtain ⟨hyo, hyp⟩ := hyif
          refine WP.loop_exit (by wram_simp [Cond.holds_lt, hyp, hyE]) ⟨?_, ?_⟩
          · simp only [stepsWork, stepWords, List.flatMap_cons, List.length_append, hea,
              Array.length_toList, ← hc']
            omega
          · rw [hyo]; simp [CNF.checkLRATAux, hpr, c']
        · simp only [hpr, ↓reduceIte] at hyif
          obtain ⟨hyp, hys, hyo, hytab, hyfr, hym⟩ := hyif
          obtain ⟨z, hz, hzo⟩ := ih ((i, c') :: db) y (s + 1)
            ⟨hy0, hy1, by regs_frame, hyE, hyT, hys, by rw [hyo, hinv.out], hytab, hyfr,
              List.forall_mem_cons.mpr ⟨hcl, hinv.dbM⟩,
              hw, by rw [hyp]; have := hinv.stamp_le; omega⟩
            (by
              rw [hyp]
              have := hlr.frame (mem' := y.mem) fun a _ ha => hym a (by
                simp only [stepWords, hea] at ha; omega)
              convert this using 1
              rw [hea]; omega)
            (by rw [hyp]; simp only [stepWords]; omega)
            (fun v hv => hM v (List.mem_append_right _ hv))
          refine WP.of_execWithin hz ⟨?_, by rw [hzo]; simp [CNF.checkLRATAux, hpr, c']⟩
          simp only [stepsWork, stepWords, List.flatMap_cons, List.length_append, hea,
            Array.length_toList, ← hc'] at hz ⊢
          omega
      · intro h hh; have := hhM h hh; omega
      · have := hinv.stamp_le; omega
    | addRat i c p hints rh =>
      simp only [encodeAction] at hla hMa hpT
      obtain ⟨htag, -⟩ := holdsList_cons_iff.mp hla
      unfold reject
      wram_exec [htag, hinv.zero, hinv.one, hinv.three, hinv.endp]
      refine WP.loop_exit (by wram_simp [Cond.holds_lt, hinv.endp]) ?_
      wram_simp
      exact ⟨by simp [stepsWork, encodeAction]; omega, by simp [CNF.checkLRATAux]⟩
    | del ids =>
      simp only [encodeAction] at hla hMa hpT
      obtain ⟨htag, hla⟩ := holdsList_cons_iff.mp hla
      have hlen : (encodeNums ids.toList).length = ids.size + 1 := by simp [encodeNums]
      simp only [List.length_cons, hlen] at hpT
      wram_exec [htag, hinv.zero, hinv.one, hinv.three]
      wram_call (delStep_spec (w := w) db ids.toList _ M T s)
        [hinv.zero, hinv.one, hinv.tbase, hla, hinv.table, hinv.fresh, hw]
        with y ⟨hyp, hytab, hyfr, hy0, hy1, hyT, hym⟩
      · wram_simp at hyp hym
        obtain ⟨z, hz, hzo⟩ := ih (db.filter fun e => !ids.toList.contains e.1) y s
          ⟨hy0, hy1, by regs_frame, by regs_frame, hyT, by regs_frame, by regs_frame,
            hytab, hyfr,
            fun e he l hl => hinv.dbM e (List.mem_of_mem_filter he) l hl, hw,
            by rw [hyp]; have := hinv.stamp_le; omega⟩
          (by
            rw [hyp]
            have hea : (encodeAction (.del ids)).length = ids.size + 2 := by
              simp [encodeAction, encodeNums]
            have := hlr.frame (mem' := y.mem) fun a _ ha => hym a (by
              simp only [stepWords] at hpT ha; omega)
            convert this using 1
            simp; omega)
          (by rw [hyp]; simp at hpT ⊢; omega)
          (fun v hv => hM v (List.mem_append_right _ hv))
        refine WP.of_execWithin hz ⟨?_, by rw [hzo]; simp [CNF.checkLRATAux]⟩
        simp [stepsWork, encodeAction, encodeNums]; omega
      · wram_simp; simp; omega
      · intro h hh; have := hMa h (by simp [encodeNums, hh]); omega

end Specs

end Cslib.Algorithms.WordRAM.LRAT

end
