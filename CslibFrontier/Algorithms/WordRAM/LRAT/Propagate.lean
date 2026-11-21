/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.LRAT.Scan

/-!
# An LRAT checker on the word RAM: unit propagation along hints

This file proves that the propagation loop of the word-RAM LRAT checker
(`Cslib.Algorithms.WordRAM.LRAT.propagate`) computes `Cslib.Logic.PL.CNF.propagateHints`.

The database of numbered clauses is represented by a table (`TableAt`): the cell `T + 2 i` holds
the address of the encoding of the clause numbered `i`, found by `List.find?` as
`propagateHints` finds it, or `0`. The trail is represented by stamps (`TrailAt`): the cell
`T + 2 c + 1` of the literal with code `c` holds the current stamp exactly when the literal is on
the trail, and never more than the stamp.

## Main definitions

* `Cslib.Algorithms.WordRAM.LRAT.TableAt`, `Cslib.Algorithms.WordRAM.LRAT.TrailAt`: the memory
  representation of the database and the trail.
* `Cslib.Algorithms.WordRAM.LRAT.hintsWork`: the total length of the hinted clauses.

## Main results

* `Cslib.Algorithms.WordRAM.LRAT.propagate_spec`: the propagation loop computes
  `propagateHints` within `40 k + 20 W + 10` instructions for `k` hints whose clauses have total
  length `W`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.LRAT

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Algorithms.WordRAM.ClauseCode Reg

/-! ### The memory representation -/

/-- The cell of the table for clause number `i`. -/
abbrev tcell (T i : ℕ) : ℕ := T + (i + i)

/-- The cell of the assignment for the literal with code `c`. -/
abbrev acell (T c : ℕ) : ℕ := T + (c + c + 1)

/-- The table at base `T` represents the database `db`: the cell of a clause number holds `0`
when `db` has no clause of that number, and otherwise the address, below `T`, of the encoding of
the first such clause. -/
def TableAt (mem : ℕ → ℕ) (T : ℕ) (db : List (ℕ × Clause ℕ)) : Prop :=
  ∀ i, (db.find? (·.1 == i) = none → mem (tcell T i) = 0) ∧
    ∀ e, db.find? (·.1 == i) = some e → 0 < mem (tcell T i) ∧
      mem (tcell T i) + e.2.length + 1 ≤ T ∧ HoldsList (mem (tcell T i)) (encodeClause e.2) mem

/-- The assignment at base `T` represents the trail `trail` with stamp `s`: the cell of a literal
holds `s` exactly when the literal is on the trail, and never more than `s`. -/
def TrailAt (mem : ℕ → ℕ) (T s : ℕ) (trail : List (Literal ℕ)) : Prop :=
  ∀ l, (mem (acell T (litCode l)) = s ↔ l ∈ trail) ∧ mem (acell T (litCode l)) ≤ s

/-- Memory `mem'` differs from `mem` only in assignment cells. -/
def OnlyAsg (T : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ∀ a, mem' a ≠ mem a → ∃ c, a = acell T c

theorem OnlyAsg.refl (T : ℕ) (mem : ℕ → ℕ) : OnlyAsg T mem mem := fun _ h => (h rfl).elim

theorem OnlyAsg.trans {T : ℕ} {m₁ m₂ m₃ : ℕ → ℕ} (h₁ : OnlyAsg T m₁ m₂) (h₂ : OnlyAsg T m₂ m₃) :
    OnlyAsg T m₁ m₃ := fun a h => by
  by_cases h' : m₃ a = m₂ a
  · exact h₁ a (h' ▸ h)
  · exact h₂ a h'

theorem OnlyAsg.update (T c v : ℕ) (mem : ℕ → ℕ) :
    OnlyAsg T mem (Function.update mem (acell T c) v) := fun a h => by
  by_cases ha : a = acell T c
  · exact ⟨c, ha⟩
  · exact (h (Function.update_of_ne ha _ _)).elim

theorem OnlyAsg.eq_of_lt {T : ℕ} {mem mem' : ℕ → ℕ} (h : OnlyAsg T mem mem') {a : ℕ} (ha : a < T) :
    mem' a = mem a := by
  by_contra hne
  obtain ⟨c, rfl⟩ := h a hne
  simp only [acell] at ha
  omega

theorem OnlyAsg.tcell_eq {T : ℕ} {mem mem' : ℕ → ℕ} (h : OnlyAsg T mem mem') (i : ℕ) :
    mem' (tcell T i) = mem (tcell T i) := by
  by_contra hne
  obtain ⟨c, hc⟩ := h _ hne
  simp only [tcell, acell] at hc
  omega

/-- The table survives changes to the assignment. -/
theorem TableAt.of_onlyAsg {mem mem' : ℕ → ℕ} {T : ℕ} {db : List (ℕ × Clause ℕ)}
    (h : TableAt mem T db) (hm : OnlyAsg T mem mem') : TableAt mem' T db := by
  intro i
  refine ⟨fun hn => by rw [hm.tcell_eq]; exact (h i).1 hn, fun e he => ?_⟩
  obtain ⟨hpos, hlt, hl⟩ := (h i).2 e he
  rw [hm.tcell_eq]
  refine ⟨hpos, hlt, hl.frame fun a _ ha => hm.eq_of_lt ?_⟩
  simp only [encodeClause, encodeClauseBy, List.length_cons, List.length_map] at ha
  omega

/-- Assigning a literal the stamp puts it on the trail. -/
theorem TrailAt.update {mem : ℕ → ℕ} {T s : ℕ} {trail : List (Literal ℕ)}
    (h : TrailAt mem T s trail) (l : Literal ℕ) :
    TrailAt (Function.update mem (acell T (litCode l)) s) T s (l :: trail) := by
  intro l'
  by_cases hl : l' = l
  · subst hl; simp
  · have : acell T (litCode l') ≠ acell T (litCode l) := by
      intro he
      simp only [acell] at he
      exact hl (litCodeBy_injective Function.injective_id (show litCode l' = litCode l by omega))
    rw [Function.update_of_ne this]
    simpa [hl] using h l'

/-! ### Work -/

/-- The length of the clause the hint `h` names in `db`, or `0`. -/
def hintLen (db : List (ℕ × Clause ℕ)) (h : ℕ) : ℕ :=
  ((db.find? (·.1 == h)).map (·.2.length)).getD 0

/-- The total length of the clauses the hints name. -/
def hintsWork (db : List (ℕ × Clause ℕ)) (hs : List ℕ) : ℕ :=
  (hs.map (hintLen db)).sum

/-! ### Scanning a hinted clause -/

section Specs

variable {w : ℕ}

/-- A contract extended with the registers the program preserves. -/
theorem exists_execWithin_preserves {c : Code .standard 28} {x : Data 28} {T : ℕ}
    {P : Data 28 → Prop} (h : ∃ y, ExecWithin w c x y T ∧ P y) :
    ∃ y, ExecWithin w c x y T ∧ P y ∧ ∀ i, c.Preserves i → y.regs i = x.regs i := by
  obtain ⟨y, hy, hP⟩ := h
  exact ⟨y, hy, hP, fun _ hi => hy.regs_eq hi⟩

/-- **Scanning a clause** at `cl` leaves in `has`, `unit` and `bad` the abstract state of its
literals that `F` does not mark, and leaves memory unchanged. -/
theorem scanClause_spec (F : Literal ℕ → Bool) (c : Clause ℕ) (x : Data 28) (M : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcl : HoldsList (x.regs cl) (encodeClause c) x.mem)
    (hF : ∀ l ∈ c, (x.mem (x.regs tbase + (litCode (Std.Sat.Literal.negate l) +
      litCode (Std.Sat.Literal.negate l) + 1)) = x.regs stamp ↔ F l = true))
    (hM : ∀ l ∈ c, litCode l + 1 ≤ M) (hw : Fits w (x.regs tbase + 2 * M + 2))
    (hlw : Fits w (x.regs cl + 1 + c.length)) :
    ∃ y, ExecWithin w scanClause x y (20 * c.length + 9) ∧ y.mem = x.mem ∧
      y.regs has = (scanOf (c.filter fun l => !F l)).found.toNat ∧
      y.regs unit = (scanOf (c.filter fun l => !F l)).code ∧
      y.regs bad = (scanOf (c.filter fun l => !F l)).conflict.toNat ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = x.regs tbase ∧
      y.regs stamp = x.regs stamp := by
  obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp hcl
  have : Fits w (x.regs cl + 1) := hlw.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold scanClause
  wram_exec [hlen, hone, hzero]
  wram_call (litLoop_spec (w := w) F c ⟨false, 0, false⟩ _ M (by wram_simp [hzero])
    (by wram_simp [hone]) (by wram_simp; exact hlits) (by wram_simp)
    (fun l hl => by wram_simp; exact hF l hl) (by wram_simp; rfl) (by wram_simp) (by wram_simp; rfl)
    hM (by wram_simp; exact hw) (by wram_simp; exact hlw))
    with y ⟨hym, hyh, hyu, hyb, -, hy0, hy1, hyt, hys, -⟩
  rw [scanLits_eq] at hyh hyu hyb
  refine ⟨by omega, by simpa using hym, hyh, hyu, hyb, hy0, hy1, by wram_simp at hyt; exact hyt,
    by wram_simp at hys; exact hys⟩

/-- The trail marks of a trail: `F l` says that the complement of `l` is on the trail. -/
abbrev falseOn (trail : List (Literal ℕ)) (l : Literal ℕ) : Bool :=
  trail.contains (Std.Sat.Literal.negate l)

theorem TrailAt.falseOn_iff {mem : ℕ → ℕ} {T s : ℕ} {trail : List (Literal ℕ)}
    (h : TrailAt mem T s trail) (l : Literal ℕ) :
    mem (T + (litCode (Std.Sat.Literal.negate l) + litCode (Std.Sat.Literal.negate l) + 1)) = s ↔
      falseOn trail l = true := by
  simpa [falseOn] using (h (Std.Sat.Literal.negate l)).1

/-- **The hint loop** computes `propagateHints db trail hints` for the hints in `[ptr, hend)`,
changing only assignment cells, and leaves `ptr` at `hend`. -/
theorem hintLoop_spec (db : List (ℕ × Clause ℕ)) (hints : List ℕ) (trail : List (Literal ℕ))
    (x : Data 28) (M T s : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (hT : x.regs tbase = T)
    (hst : x.regs stamp = s) (hres : x.regs res = 0)
    (hl : HoldsList (x.regs ptr) hints x.mem) (hhe : x.regs hend = x.regs ptr + hints.length)
    (hhT : x.regs hend ≤ T)
    (htab : TableAt x.mem T db) (htr : TrailAt x.mem T s trail)
    (hhM : ∀ h ∈ hints, h ≤ M) (hdbM : ∀ e ∈ db, ∀ l ∈ e.2, litCode l + 1 ≤ M)
    (hw : Fits w (T + 2 * M + 2)) :
    ∃ y, ExecWithin w hintLoop x y (40 * hints.length + 20 * hintsWork db hints + 2) ∧
      y.regs res = (CNF.propagateHints db trail hints).toNat ∧ y.regs ptr = x.regs hend ∧
      OnlyAsg T x.mem y.mem ∧ (∃ trail', TrailAt y.mem T s trail') ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = T ∧ y.regs stamp = s ∧
      y.regs hend = x.regs hend := by
  induction hints generalizing x trail with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simp [hres, CNF.propagateHints_nil],
      by simp [hhe], OnlyAsg.refl _ _, ⟨trail, htr⟩, hzero, hone, hT, hst, rfl⟩
    simp [Cond.holds_lt, hhe]
  | cons h hints ih =>
    simp only [List.length_cons] at hhe
    have hc : (Cond.lt ptr hend).Holds x := by simp only [Cond.holds_lt, hhe]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp hl
    have hhM' := hhM h (by simp)
    have : Fits w (h + h) := hw.of_le (by omega)
    have : Fits w (T + (h + h)) := hw.of_le (by omega)
    have : Fits w (x.regs ptr + 1) := hw.of_le (by omega)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold hintBody
    rcases hfind : db.find? (·.1 == h) with _ | e
    · have h0 : x.mem (T + (h + h)) = 0 := (htab h).1 hfind
      wram_exec [hlit, hone, hT, h0, hzero]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt])) ?_
      wram_simp
      refine ⟨?_, by simp [hres, CNF.propagateHints_cons, hfind], OnlyAsg.refl _ _, ⟨trail, htr⟩,
        hzero, hone, hT, hst⟩
      simp only [List.length_cons]; omega
    · obtain ⟨hpos, hltT, hcl⟩ := (htab h).2 e hfind
      simp only [tcell] at hpos hltT hcl
      have he : e ∈ db := List.mem_of_find?_eq_some hfind
      have : Fits w (x.mem (T + (h + h))) := hw.of_le (by omega)
      have hne : x.mem (T + (h + h)) ≠ 0 := by omega
      wram_exec [hlit, hone, hT, hzero, hne]
      wram_call (exists_execWithin_preserves (scanClause_spec (w := w) (falseOn trail) e.2 _ M
        (by wram_simp [hzero]) (by wram_simp [hone]) (by wram_simp [hT]; exact hcl)
        (fun l _ => by wram_simp [hT, hst]; exact htr.falseOn_iff l) (hdbM e he)
        (by wram_simp [hT]; exact hw) (by wram_simp [hT]; exact hw.of_le (by omega))))
        with y ⟨⟨hym, hyh, hyu, hyb, hy0, hy1, hyt, hys⟩, hpres⟩
      have hyhe := hpres hend (by decide)
      have hyres := hpres res (by decide)
      wram_simp at hym hyt hys hyhe hyres
      rw [hT] at hyt; rw [hst] at hys
      have hwork : hintsWork db (h :: hints) = e.2.length + hintsWork db hints := by
        simp [hintsWork, hintLen, hfind]
      simp only [falseOn] at hyh hyu hyb
      unfold afterScan
      rcases hf : e.2.filter (fun l => !trail.contains (Std.Sat.Literal.negate l)) with _ | ⟨l, ls⟩
      · simp only [hf, scanOf, Bool.toNat_false] at hyh hyu hyb
        wram_exec [hyb, hyh, hy0, hy1]
        refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt]))
          ⟨?_, ?_, ?_, ?_, ⟨trail, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hwork]; simp only [List.length_cons]; omega
        · wram_simp; simp only [CNF.propagateHints_cons, hfind, hf]; rfl
        all_goals wram_simp
        all_goals first
          | exact hyhe | exact hy0 | exact hy1 | exact hyt | exact hys
          | (rw [hym]; exact OnlyAsg.refl _ _) | (rw [hym]; exact htr)
      · have hlmem : l ∈ e.2 := List.mem_of_mem_filter (l := e.2) (hf ▸ List.mem_cons_self ..)
        have hlM := hdbM e he l hlmem
        by_cases hall : ls.all (· == l) = true
        · simp only [hf, scanOf, hall, Bool.not_true, Bool.toNat_false, Bool.toNat_true]
            at hyh hyu hyb
          have : Fits w (litCode l + litCode l) := hw.of_le (by omega)
          have : Fits w (litCode l + litCode l + 1) := hw.of_le (by omega)
          have : Fits w (T + (litCode l + litCode l + 1)) := hw.of_le (by omega)
          have hyptr := hpres ptr (by decide)
          wram_simp at hyptr
          wram_exec [hyb, hyh, hy0, hy1, hyu, hyt, hT]
          have hOA : OnlyAsg T x.mem (Function.update x.mem (acell T (litCode l)) s) :=
            OnlyAsg.update T _ s x.mem
          refine WP.name fun x' hx' => ?_
          have hih := ih (l :: trail) x' (by subst hx'; wram_simp [hy0])
            (by subst hx'; wram_simp [hy1]) (by subst hx'; wram_simp [hyt])
            (by subst hx'; wram_simp [hys]) (by subst hx'; wram_simp [hyres, hres])
            (by
              subst hx'; wram_simp [hyptr, hym, hys]
              exact hrest.frame fun a _ ha => hOA.eq_of_lt (by omega))
            (by subst hx'; wram_simp [hyptr, hyhe, hhe]; omega)
            (by subst hx'; wram_simp [hyhe]; omega)
            (by subst hx'; wram_simp [hym, hys]; exact htab.of_onlyAsg hOA)
            (by subst hx'; wram_simp [hym, hys]; exact htr.update l)
            (fun h' hh' => hhM h' (by simp [hh']))
          obtain ⟨z, hz, hzres, hzptr, hzoa, hztr, hz0, hz1, hzT, hzs, hzhe⟩ := hih
          subst hx'
          refine WP.of_execWithin hz ?_
          wram_simp at hzptr hzoa hzhe
          refine ⟨?_, ?_, ?_, ?_, hztr, hz0, hz1, hzT, hzs, ?_⟩
          · rw [hwork]; simp only [List.length_cons]; omega
          · rw [hzres]; simp only [CNF.propagateHints_cons, hfind, hf, hall]; rfl
          · rw [hzptr, hyhe]
          · rw [hym, hys] at hzoa; exact hOA.trans hzoa
          · rw [hzhe, hyhe]
        · simp only [hf, scanOf, hall, Bool.not_false, Bool.toNat_true] at hyh hyu hyb
          wram_exec [hyb, hy0, hy1]
          refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt]))
            ⟨?_, ?_, ?_, ?_, ⟨trail, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hwork]; simp only [List.length_cons]; omega
          · wram_simp
            rw [hyres, hres]
            simp only [Bool.not_eq_true] at hall
            simp only [CNF.propagateHints_cons, hfind, hf, hall]; rfl
          all_goals wram_simp
          all_goals first
            | exact hyhe | exact hy0 | exact hy1 | exact hyt | exact hys
            | (rw [hym]; exact OnlyAsg.refl _ _) | (rw [hym]; exact htr)

/-- **Unit propagation along hints**: from the hints `encodeNums hints` at `ptr`, `propagate`
leaves `propagateHints db trail hints` in `res` and `ptr` past the hints, changing only
assignment cells. -/
theorem propagate_spec (db : List (ℕ × Clause ℕ)) (hints : List ℕ) (trail : List (Literal ℕ))
    (x : Data 28) (M T s : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (hT : x.regs tbase = T)
    (hst : x.regs stamp = s)
    (hl : HoldsList (x.regs ptr) (encodeNums hints) x.mem)
    (hpT : x.regs ptr + 1 + hints.length ≤ T)
    (htab : TableAt x.mem T db) (htr : TrailAt x.mem T s trail)
    (hhM : ∀ h ∈ hints, h ≤ M) (hdbM : ∀ e ∈ db, ∀ l ∈ e.2, litCode l + 1 ≤ M)
    (hw : Fits w (T + 2 * M + 2)) :
    ∃ y, ExecWithin w propagate x y (40 * hints.length + 20 * hintsWork db hints + 6) ∧
      y.regs res = (CNF.propagateHints db trail hints).toNat ∧
      y.regs ptr = x.regs ptr + 1 + hints.length ∧
      OnlyAsg T x.mem y.mem ∧ (∃ trail', TrailAt y.mem T s trail') ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = T ∧ y.regs stamp = s := by
  obtain ⟨hlen, hrest⟩ := holdsList_cons_iff.mp hl
  have : Fits w (x.regs ptr + 1) := hw.of_le (by omega)
  have : Fits w (x.regs ptr + 1 + hints.length) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold propagate
  wram_exec [hlen, hone, hzero]
  wram_call (hintLoop_spec (w := w) db hints trail _ M T s (by wram_simp [hzero])
    (by wram_simp [hone]) (by wram_simp [hT]) (by wram_simp [hst]) (by wram_simp [hzero])
    (by wram_simp; exact hrest) (by wram_simp) (by wram_simp; omega) (by wram_simp; exact htab)
    (by wram_simp; exact htr) hhM hdbM hw)
    with y ⟨hyres, hyptr, hyoa, hytr, hy0, hy1, hyT, hys, -⟩
  wram_simp at hyptr hyoa
  exact ⟨by omega, hyres, hyptr, hyoa, hytr, hy0, hy1, hyT, hys⟩

end Specs

end Cslib.Algorithms.WordRAM.LRAT

end
