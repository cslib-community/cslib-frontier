/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Scan
import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop

/-!
# The DPLL solver on the word RAM: the steps

This file proves that one iteration of the main loop of the word-RAM DPLL solver performs one step
of the search with an explicit trail (`Cslib.Algorithms.WordRAM.DPLL.stepBody_spec`): the memory
holds the trail as a literal array and as a stack of entries
(`Cslib.Algorithms.WordRAM.DPLL.StateAt`), and the step either moves to the memory of the next
trail or writes the output.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Algorithms.WordRAM.ClauseCode Cslib.Algorithms.Lean.DPLL Reg

theorem length_vars_le (φ : CNF ℕ) : φ.vars.length ≤ (φ.flatMap encodeClause).length := by
  induction φ with
  | nil => simp [CNF.vars]
  | cons c φ ih =>
    simp only [CNF.vars, List.flatten_cons, List.map_append, List.length_append,
      List.length_map, List.flatMap_cons, length_encodeClauseBy] at ih ⊢
    omega

/-! ### The memory of a trail -/

/-- The words of the trail: two per entry, bottom first, the code of its literal and `1` for a
second branch. -/
def trailWords (t : Trail) : List ℕ :=
  t.reverse.flatMap fun e => [litCode e.lit, e.isSecond.toNat]

theorem trailWords_cons (e : TrailEntry) (t : Trail) :
    trailWords (e :: t) = trailWords t ++ [litCode e.lit, e.isSecond.toNat] := by
  simp [trailWords]

theorem length_trailWords (t : Trail) : (trailWords t).length = 2 * t.length := by
  induction t with
  | nil => rfl
  | cons e t ih => rw [trailWords_cons]; simp [ih]; omega

/-- The variable of a trail entry. -/
def entryVar : TrailEntry → ℕ
  | ⟨(v, _), _⟩ => v

@[simp] theorem entryVar_mk (l : Literal ℕ) (b : Bool) : entryVar ⟨l, b⟩ = l.1 := rfl

/-- The trail invariant: the variables of the trail are distinct variables of the formula. -/
def TrailOK (φ : CNF ℕ) (t : Trail) : Prop :=
  (t.map entryVar).Nodup ∧ ∀ e ∈ t, entryVar e ∈ φ.vars

theorem assigned_lits_iff {t : Trail} {v : ℕ} :
    Assigned (Trail.lits t) v = true ↔ v ∈ t.map entryVar := by
  induction t with
  | nil => simp [Assigned, Trail.lits]
  | cons e t ih =>
    obtain ⟨⟨u, b⟩, c⟩ := e
    simp only [Trail.lits_cons, assigned_cons, Bool.or_eq_true, ih, beq_iff_eq, List.map_cons,
      List.mem_cons]
    tauto

/-- The memory of a trail: the clauses from address `2` to `T`, the literal array at `T`, and the
trail entries at `T + 2 N`. -/
structure MemAt (φ : CNF ℕ) (N T : ℕ) (mem : ℕ → ℕ) (t : Trail) : Prop where
  clauses : HoldsList 2 (φ.flatMap encodeClause) mem
  hT : 2 + (φ.flatMap encodeClause).length = T
  vars : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N
  lits : LitArr mem T N (Trail.lits t)
  trail : HoldsList (T + 2 * N) (trailWords t) mem
  ok : TrailOK φ t

theorem mem_vars_lt {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {t : Trail} (h : MemAt φ N T mem t)
    {v : ℕ} (hv : v ∈ φ.vars) : v < N := by
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.1 hv
  exact h.vars c hc _ hl

theorem lits_not_mem {φ : CNF ℕ} {l : Literal ℕ} {b : Bool} {t : Trail}
    (h : TrailOK φ (⟨l, b⟩ :: t)) :
    l ∉ Trail.lits t ∧ Std.Sat.Literal.negate l ∉ Trail.lits t := by
  have hn : l.1 ∉ t.map entryVar := (List.nodup_cons.1 h.1).1
  have key : ∀ l' ∈ Trail.lits t, l'.1 ≠ l.1 := fun l' hl' he => by
    obtain ⟨⟨l₀, b₀⟩, hee, hel⟩ := List.mem_map.1 hl'
    exact hn (List.mem_map.2 ⟨⟨l₀, b₀⟩, hee, by simp only [entryVar_mk]; rw [← he, ← hel]⟩)
  exact ⟨fun hm => key l hm rfl, fun hm => key _ hm rfl⟩

/-- Updating a cell of the literal array. -/
theorem LitArr.update {mem : ℕ → ℕ} {T N : ℕ} {π π' : List (Literal ℕ)} (h : LitArr mem T N π)
    (l : Literal ℕ) (v : ℕ) (hv : v = (π'.contains l).toNat)
    (hπ : ∀ l', l' ≠ l → π'.contains l' = π.contains l') :
    LitArr (Function.update mem (T + litCode l) v) T N π' := by
  intro l' hl'
  by_cases he : l' = l
  · subst he; simp [hv]
  · have : T + litCode l' ≠ T + litCode l := by
      intro h'
      exact he (litCodeBy_injective Function.injective_id (show litCode l' = litCode l by omega))
    rw [Function.update_of_ne this, h l' hl', hπ l' he]

/-- Cells at or above `T + 2 N` are outside the literal array. -/
theorem LitArr.update_ge {mem : ℕ → ℕ} {T N : ℕ} {π : List (Literal ℕ)} (h : LitArr mem T N π)
    {a : ℕ} (ha : T + 2 * N ≤ a) (v : ℕ) : LitArr (Function.update mem a v) T N π := by
  intro l hl
  have := litCode_lt hl
  rw [Function.update_of_ne (by omega)]
  exact h l hl

/-- **Pushing an entry** `⟨l, b⟩` on a variable of the formula not on the trail: the new memory
sets the literal's cell to `1` and writes the entry's two words above the trail, and agrees with
the old memory elsewhere. -/
theorem MemAt.cons {φ : CNF ℕ} {N T : ℕ} {mem mem' : ℕ → ℕ} {t : Trail} (h : MemAt φ N T mem t)
    {l : Literal ℕ} {b : Bool} (hl : l.1 ∈ φ.vars) (hnot : l.1 ∉ t.map entryVar)
    (hmem : ∀ a, mem' a =
      if a = T + litCode l then 1
      else if a = T + 2 * N + 2 * t.length then litCode l
      else if a = T + 2 * N + 2 * t.length + 1 then b.toNat
      else mem a) :
    MemAt φ N T mem' (⟨l, b⟩ :: t) := by
  have hlN := mem_vars_lt h hl
  have hc := litCode_lt hlN
  have hT := h.hT
  -- Cells away from the three written ones keep their contents.
  have hframe : ∀ a, a ≠ T + litCode l → a ≠ T + 2 * N + 2 * t.length →
      a ≠ T + 2 * N + 2 * t.length + 1 → mem' a = mem a := fun a h₁ h₂ h₃ => by
    simp [hmem, h₁, h₂, h₃]
  refine ⟨h.clauses.frame fun a _ ha' => hframe a (by omega) (by omega) (by omega), h.hT,
    h.vars, fun l' hl' => ?_, ?_, ?_⟩
  · have hc' := litCode_lt hl'
    by_cases he : l' = l
    · subst he; simp [hmem, Trail.lits]
    · have hne : T + litCode l' ≠ T + litCode l := fun h' =>
        he (litCodeBy_injective Function.injective_id (show litCode l' = litCode l by omega))
      rw [hframe _ hne (by omega) (by omega), h.lits l' hl']
      simp [Trail.lits, he]
  · rw [trailWords_cons]
    refine holdsList_append_iff.mpr ⟨h.trail.frame fun a _ ha' => ?_, ?_⟩
    · rw [length_trailWords] at ha'
      exact hframe a (by omega) (by omega) (by omega)
    · rw [length_trailWords]
      refine holdsList_cons_iff.mpr ⟨?_, holdsList_cons_iff.mpr ⟨?_, fun i => i.elim0⟩⟩
      · rw [hmem]; split_ifs <;> first | rfl | omega
      · rw [hmem]; split_ifs <;> first | rfl | omega
  · refine ⟨List.nodup_cons.2 ⟨hnot, h.ok.1⟩, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hl
    · exact h.ok.2 e he

/-- **Pushing a first branch** on an open variable of the formula. -/
theorem MemAt.push {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {t : Trail} (h : MemAt φ N T mem t)
    {l : Literal ℕ} (hl : l.1 ∈ φ.vars) (ha : Assigned (Trail.lits t) l.1 = false) :
    MemAt φ N T (Function.update (Function.update (Function.update mem
      (T + 2 * N + 2 * t.length) (litCode l)) (T + 2 * N + 2 * t.length + 1) 0)
      (T + litCode l) 1) (⟨l, false⟩ :: t) := by
  have hc := litCode_lt (mem_vars_lt h hl)
  refine h.cons hl (by rw [← assigned_lits_iff]; simp [ha]) fun a => ?_
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem TrailOK.tail {φ : CNF ℕ} {e : TrailEntry} {t : Trail} (h : TrailOK φ (e :: t)) :
    TrailOK φ t :=
  ⟨(List.nodup_cons.1 h.1).2, fun e' he' => h.2 e' (List.mem_cons_of_mem _ he')⟩

/-- **Popping an entry**: clearing its literal. -/
theorem MemAt.pop {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {l : Literal ℕ} {b : Bool} {t : Trail}
    (h : MemAt φ N T mem (⟨l, b⟩ :: t)) :
    MemAt φ N T (Function.update mem (T + litCode l) 0) t := by
  have hlN : l.1 < N := mem_vars_lt h (h.ok.2 ⟨l, b⟩ List.mem_cons_self)
  have hc := litCode_lt hlN
  have hT := h.hT
  have hnot := (lits_not_mem h.ok).1
  have htr := (holdsList_append_iff.mp (trailWords_cons ⟨l, b⟩ t ▸ h.trail)).1
  refine ⟨h.clauses.frame fun a _ ha' => ?_, h.hT, h.vars, ?_, ?_, h.ok.tail⟩
  · rw [Function.update_of_ne (by omega)]
  · refine LitArr.update h.lits l 0 (by simp [hnot]) fun l' hl' => ?_
    simp [Trail.lits, hl']
  · exact htr.frame fun a h₁ _ => by rw [Function.update_of_ne (by omega)]

/-- **Flipping a first branch** into the second branch: popping it, then pushing its negation as
a second branch. -/
theorem MemAt.flip {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {l : Literal ℕ} {t : Trail}
    (h : MemAt φ N T mem (⟨l, false⟩ :: t)) :
    MemAt φ N T (Function.update (Function.update (Function.update (Function.update mem
      (T + litCode l) 0) (T + litCode l.negate) 1) (T + 2 * N + 2 * t.length)
      (litCode l.negate)) (T + 2 * N + 2 * t.length + 1) 1) (⟨l.negate, true⟩ :: t) := by
  have hl := h.ok.2 ⟨l, false⟩ List.mem_cons_self
  have hnc := litCode_lt (l := l.negate) (mem_vars_lt h hl)
  refine h.pop.cons (l := l.negate) hl (List.nodup_cons.1 h.ok.1).1 fun a => ?_
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem TrailOK.length_le_vars {φ : CNF ℕ} {t : Trail} (h : TrailOK φ t) :
    t.length ≤ φ.vars.length := by
  have := (h.1.subperm fun v hv => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
    exact h.2 e he).length_le
  simpa using this

theorem TrailOK.length_le {φ : CNF ℕ} {t : Trail} (h : TrailOK φ t) {N : ℕ}
    (hN : ∀ v ∈ φ.vars, v < N) : t.length ≤ N := by
  have := (h.1.subperm (l₂ := List.range N) fun v hv => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
    exact List.mem_range.2 (hN _ (h.2 e he))).length_le
  simpa using this

/-- **The state at the head of the main loop** for the trail `t`: the constants, the bases of the
arrays, the top of the trail, and the memory of the trail. -/
def StateAt (φ : CNF ℕ) (N T : ℕ) (x : Data 32) (t : Trail) : Prop :=
  x.regs zero = 0 ∧ x.regs one = 1 ∧ x.regs two = 2 ∧ x.regs tb = T ∧ x.regs cend = T ∧
    x.regs sb = T + 2 * N ∧ x.regs ob = T + 4 * N ∧ x.regs nv = N ∧ x.regs go = 1 ∧
    x.regs tp = T + 2 * N + 2 * t.length ∧ MemAt φ N T x.mem t

/-- The trail without the second branches on top. -/
def dropSecond : Trail → Trail
  | ⟨_, true⟩ :: t => dropSecond t
  | t => t

theorem backtrack_eq (t : Trail) :
    Trail.backtrack t = match dropSecond t with
      | [] => none
      | ⟨l, _⟩ :: t' => some (⟨l.negate, true⟩ :: t') := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨l, b⟩ := e
    cases b
    · rfl
    · rw [Trail.backtrack_cons_true, ih]; rfl

theorem dropSecond_cons_true (l : Literal ℕ) (t : Trail) :
    dropSecond (⟨l, true⟩ :: t) = dropSecond t := rfl

theorem dropSecond_cons_false (l : Literal ℕ) (t : Trail) :
    dropSecond (⟨l, false⟩ :: t) = ⟨l, false⟩ :: t := rfl

theorem dropSecond_eq_cons {t t' : Trail} {l : Literal ℕ} {b : Bool}
    (h : dropSecond t = ⟨l, b⟩ :: t') : b = false := by
  induction t with
  | nil => cases h
  | cons e t ih =>
    obtain ⟨l', b'⟩ := e
    cases b'
    · rw [dropSecond_cons_false] at h; cases h; rfl
    · exact ih h

theorem length_dropSecond_le (t : Trail) : (dropSecond t).length ≤ t.length := by
  induction t with
  | nil => exact le_rfl
  | cons e t ih =>
    obtain ⟨l, b⟩ := e
    cases b
    · exact le_rfl
    · rw [dropSecond_cons_true]; simp only [List.length_cons]; omega

/-- The two words of the top entry of a trail. -/
theorem MemAt.top {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {l : Literal ℕ} {b : Bool} {t : Trail}
    (h : MemAt φ N T mem (⟨l, b⟩ :: t)) :
    mem (T + 2 * N + 2 * t.length) = litCode l ∧
      mem (T + 2 * N + 2 * t.length + 1) = b.toNat := by
  have := (holdsList_append_iff.mp (trailWords_cons ⟨l, b⟩ t ▸ h.trail)).2
  rw [length_trailWords] at this
  obtain ⟨h₁, h₂⟩ := holdsList_cons_iff.mp this
  exact ⟨h₁, (holdsList_cons_iff.mp h₂).1⟩

theorem litCode_true (v : ℕ) : litCode (v, true) = v + v + 1 := by
  simp [litCodeBy]; omega

/-- The output of a model: `1`, then the bits of the true literals of `π` below `N`. -/
def modelWords (N : ℕ) (π : List (Literal ℕ)) : List ℕ :=
  1 :: (List.range N).map fun v => (assignment π v).toNat

/-- The output for an answer of the search. -/
def answerList (N : ℕ) : Trail.Answer → List ℕ
  | .sat π => modelWords N π
  | .unsat => [0]

/-- The code of the literal pushed by a branching, from the scan registers: that of the unit
clause, or else the first open variable, true. -/
theorem branchCode_eq (φ : CNF ℕ) (π : List (Literal ℕ)) {uf' unit' ov' : ℕ}
    (huf : uf' = ((unitLiteral? φ π).map litCode).isSome.toNat)
    (hunit : unit' = ((unitLiteral? φ π).map litCode).getD 0)
    (hov : ov' = (φ.vars.find? fun x => !Assigned π x).getD 0) :
    (if uf' = 0 then ov' + ov' + 1 else unit') = litCode (nextLiteral φ π) := by
  rw [huf, hunit, hov]
  unfold nextLiteral
  cases hu : unitLiteral? φ π with
  | some l => simp
  | none => simp [litCode_true]

/-- The instructions of one step: a pass over the clauses, then backtracking, branching, or
writing the model. -/
def stepTime (φ : CNF ℕ) (N : ℕ) (t : Trail) : ℕ :=
  23 * (φ.flatMap encodeClause).length + 14 * t.length + 60 +
    match Trail.step φ t with
    | .inr _ => 0
    | .inl _ => 10 * N

section Specs

variable {w : ℕ}

attribute [local wram_simps] StateAt ScanAt Bool.toNat_false Bool.toNat_true

/-- **Branching** pushes the literal `l` given by the scan registers, and changes no cell from
`T + 4 N + 2` on. -/
theorem push_spec (φ : CNF ℕ) (N T : ℕ) (x : Data 32) (t : Trail) (l : Literal ℕ)
    (hs : StateAt φ N T x t)
    (hcode : (if x.regs uf = 0 then x.regs ov + x.regs ov + 1 else x.regs unit) = litCode l)
    (hl : l.1 ∈ φ.vars) (ha : Assigned (Trail.lits t) l.1 = false)
    (hfit : Fits w (T + 5 * N + 2)) :
    ∃ y, ExecWithin w push x y 12 ∧ StateAt φ N T y (⟨l, false⟩ :: t) ∧
      ∀ a, T + 4 * N + 2 ≤ a → y.mem a = x.mem a := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := hs
  have hpush := hmem.push hl ha
  have hlen := hpush.ok.length_le fun v hv => mem_vars_lt hmem hv
  simp only [List.length_cons] at hlen
  have hc := litCode_lt (mem_vars_lt hmem hl)
  refine WP.exists_execWithin ?_
  unfold push
  split_ifs at hcode with hu <;> wram_exec [*] <;> refine ⟨?_, fun a ha => ?_⟩ <;>
    wram_simp [*, List.length_cons] <;> omega

/-- **The pop loop** drops the second branches on top of the trail, and changes no cell from
`T + 4 N + 2` on. -/
theorem popLoop_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (haux : x.regs aux = 1) (hfit : Fits w (T + 5 * N + 2)) :
    ∃ y, ExecWithin w popLoop x y (14 * t.length + 14) ∧ StateAt φ N T y (dropSecond t) ∧
      y.regs aux = 0 ∧ ∀ a, T + 4 * N + 2 ≤ a → y.mem a = x.mem a := by
  induction t generalizing x with
  | nil =>
    obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := hs
    have hst : ¬x.regs sb < x.regs tp := by rw [hsb, htp]; simp
    refine WP.exists_execWithin (WP.loop_iter (by simp [Cond.holds_eq, haux, h1]) ?_)
    unfold popBody
    wram_exec [hst]
    refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_eq, h1, hz])) ?_
    wram_simp [*, dropSecond]
    exact fun _ _ => trivial
  | cons e t ih =>
    obtain ⟨l, b⟩ := e
    obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := hs
    have hlen := hmem.ok.length_le fun v hv => mem_vars_lt hmem hv
    simp only [List.length_cons] at hlen
    obtain ⟨hcode, hflag⟩ := hmem.top
    have hcl := litCode_lt (mem_vars_lt hmem (hmem.ok.2 ⟨l, b⟩ List.mem_cons_self))
    replace htp : x.regs tp = T + 2 * N + 2 * t.length + 2 := by rw [htp]; simp; omega
    have hst : x.regs sb < x.regs tp := by omega
    have e1 : T + 2 * N + 2 * t.length + 2 - 1 = T + 2 * N + 2 * t.length + 1 := by omega
    have e2 : T + 2 * N + 2 * t.length + 2 - 2 = T + 2 * N + 2 * t.length := by omega
    have hpop := hmem.pop
    refine WP.exists_execWithin (WP.loop_iter (by simp [Cond.holds_eq, haux, h1]) ?_)
    unfold popBody
    cases b
    · wram_exec [*]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_eq, h1, hz])) ?_
      wram_simp [*, dropSecond_cons_false, List.length_cons]
      exact ⟨by omega, fun _ _ => trivial⟩
    · wram_exec [*]
      wram_call (ih _ ..) framed [*] with v m ⟨⟨htp', hm'⟩, ha', hfr⟩
      refine ⟨by simp only [List.length_cons]; omega, ⟨htp', hm'⟩, ha', fun a ha => ?_⟩
      rw [hfr a ha]
      simp only [Data.write_mem, Data.set_mem]
      exact Function.update_of_ne (by omega) _ _

/-- **Backtracking**: the state of the backtracked trail, or the output `[0]` at `T + 4 N`; no
cell from `T + 4 N + 2` on changes. -/
theorem backtrack_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (hfit : Fits w (T + 5 * N + 2)) :
    ∃ y, ExecWithin w backtrack x y (14 * t.length + 40) ∧
      (match Trail.backtrack t with
      | some t' => StateAt φ N T y t'
      | none => y.regs go = 0 ∧ y.regs out = T + 4 * N ∧
          outputList y.mem (T + 4 * N) = [0]) ∧
      ∀ a, T + 4 * N + 2 ≤ a → y.mem a = x.mem a := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := id hs
  refine WP.exists_execWithin ?_
  unfold backtrack
  wram_exec [h1]
  wram_call (popLoop_spec (w := w) φ N T t _ ..) framed [*] with v m ⟨⟨htp', hm'⟩, ha', hfr⟩
  have hdl := length_dropSecond_le t
  rw [backtrack_eq]
  cases hd : dropSecond t with
  | nil =>
    rw [hd] at htp' hm'
    have hst : ¬T + 2 * N < v tp := by rw [htp']; simp
    unfold outUnsat
    wram_exec [*]
    refine ⟨⟨by wram_simp [*], by wram_simp [*], ?_⟩, fun a ha => ?_⟩
    · rw [outputList_eq_iff]
      wram_simp [*]
      exact ⟨by simp, holdsList_cons_iff.mpr ⟨by simp, fun i => i.elim0⟩⟩
    · wram_simp
      simpa using hfr a ha
  | cons e t' =>
    obtain ⟨l, b⟩ := e
    obtain rfl := dropSecond_eq_cons hd
    rw [hd] at htp' hm' hdl
    simp only [List.length_cons] at hdl
    have hlen := hm'.ok.length_le fun v hv => mem_vars_lt hm' hv
    simp only [List.length_cons] at hlen
    replace htp' : v tp = T + 2 * N + 2 * t'.length + 2 := by rw [htp']; simp; omega
    have hst : T + 2 * N < v tp := by omega
    obtain ⟨hcode, -⟩ := hm'.top
    have hlN : l.1 < N := mem_vars_lt hm' (hm'.ok.2 ⟨l, false⟩ List.mem_cons_self)
    have hcl := litCode_lt hlN
    have hncl := litCode_lt (l := l.negate) hlN
    have hxor : litCode l ^^^ 1 = litCode l.negate := litCodeBy_xor_one _root_.id l
    have e2 : T + 2 * N + 2 * t'.length + 2 - 2 = T + 2 * N + 2 * t'.length := by omega
    have hflip := hm'.flip
    wram_exec [*]
    refine ⟨?_, fun a ha => ?_⟩
    · wram_simp [*, List.length_cons]
      omega
    · wram_simp
      simpa using hfr a ha

/-- **The model loop** writes the bits of the true literals of `π` for the variables below `N`
at `T + 4 N + 2`, and changes no cell below. -/
theorem outLoop_spec (π : List (Literal ℕ)) (N T : ℕ) (x : Data 32)
    (hone : x.regs one = 1) (htwo : x.regs two = 2) (htb : x.regs tb = T)
    (hob : x.regs ob = T + 4 * N) (hnv : x.regs nv = N) (hvar : x.regs var = 0)
    (hπ : LitArr x.mem T N π) (hfit : Fits w (T + 5 * N + 2)) :
    ∃ y, ExecWithin w (.loop (.lt var nv) outBody) x y (10 * N + 2) ∧
      (∀ i < N, y.mem (T + 4 * N + 2 + i) = (π.contains (i, true)).toNat) ∧
      ∀ a < T + 4 * N + 2, y.mem a = x.mem a := by
  wram_fold (fun rest y => y.regs var + rest.length = N ∧
      (∀ i < y.regs var, y.mem (T + 4 * N + 2 + i) = (π.contains (i, true)).toNat) ∧
      ∀ a < T + 4 * N + 2, y.mem a = x.mem a)
    over (List.replicate N ()) cost (fun _ => 8)
  case init => exact ⟨by simp [hvar], fun i hi => by omega, fun _ _ => rfl⟩
  case exit => rintro v m ⟨he, -⟩; omega
  case step =>
    rintro - rest v m ⟨he, hw, hm⟩
    have hvN : v var < N := by omega
    have hlit : x.mem (T + (v var + v var + 1)) = (π.contains (v var, true)).toNat := by
      rw [← litCode_true]; exact hπ (v var, true) hvN
    refine ⟨by omega, ?_⟩
    unfold outBody
    wram_exec [*]
    refine ⟨by wram_simp; omega, fun i hi => ?_, fun a ha => ?_⟩
    · wram_simp at hi
      rcases Nat.lt_or_ge i (v var) with h | h
      · wram_simp; exact hw i h
      · obtain rfl : i = v var := by omega
        wram_simp
    · wram_simp; exact hm a ha
  case post =>
    rintro v m ⟨he, hw, hm⟩
    exact ⟨by simp; omega, fun i hi => hw i (by omega), hm⟩

/-- **Writing the model** of the trail at `T + 4 N`. -/
theorem outSat_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (hfit : Fits w (T + 5 * N + 2)) :
    ∃ y, ExecWithin w outSat x y (10 * N + 10) ∧ y.regs go = 0 ∧ y.regs out = T + 4 * N ∧
      outputList y.mem (T + 4 * N) = modelWords N (Trail.lits t) := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := hs
  have hπ := (hmem.lits.update_ge (a := T + 4 * N) (by omega) (N + 1)).update_ge
    (a := T + 4 * N + 1) (by omega) 1
  refine WP.exists_execWithin ?_
  unfold outSat
  wram_exec [*]
  wram_call (outLoop_spec (w := w) (Trail.lits t) N T _ ..) framed [*] with v m ⟨hw, hm⟩
  wram_exec [*]
  refine ⟨by wram_simp [*], by wram_simp [*], ?_⟩
  wram_simp
  rw [outputList_eq_iff]
  refine ⟨?_, holdsList_cons_iff.mpr ⟨?_, fun i => ?_⟩⟩
  · rw [hm _ (by omega)]; simp [modelWords]
  · rw [hm _ (by omega)]; simp
  · have hi : i.val < N := by simpa [modelWords] using i.isLt
    change m (T + 4 * N + 1 + 1 + i.val) = _
    rw [show T + 4 * N + 1 + 1 + i.val = T + 4 * N + 2 + i.val by omega, hw i.val hi]
    have hget : ((List.range N).map fun v => (assignment (Trail.lits t) v).toNat)[i.val]'
        (by simpa using hi) = (assignment (Trail.lits t) i.val).toNat := by simp
    exact (hget.trans (by simp [assignment])).symm

/-- **One step of the search** on the word RAM: the state of the next trail, or the output of the
answer at `T + 4 N`. -/
theorem stepBody_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (hfit : Fits w (T + 5 * N + 2)) :
    ∃ y, ExecWithin w stepBody x y (stepTime φ N t) ∧
      match Trail.step φ t with
      | .inr t' => StateAt φ N T y t'
      | .inl a => y.regs go = 0 ∧ y.regs out = T + 4 * N ∧
          outputList y.mem (T + 4 * N) = answerList N a := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := id hs
  set π := Trail.lits t with hπdef
  have hT := hmem.hT
  have hcl := hmem.clauses
  have hvars := hmem.vars
  have hlits := hmem.lits
  have hlenL : t.length ≤ (φ.flatMap encodeClause).length :=
    hmem.ok.length_le_vars.trans (length_vars_le φ)
  refine WP.exists_execWithin ?_
  unfold stepBody
  refine WP.seq ?_
  wram_call (scan_spec (w := w) π φ _ N ..) framed [hz, h1, h2, htb, hce]
    with v m ⟨rfl, hconf, halls, huf, hunit, hopf, hov⟩
  have hs' : StateAt φ N T (x.havoc scan v x.mem) t := by wram_simp [*]
  unfold stepTime
  by_cases hc : φ.any (Falsifies π) = true
  · have hstep := Trail.step_of_status_eq_conflict (status_eq_conflict hc)
    rw [hc, Bool.toNat_true] at hconf
    wram_exec [hconf, h1]
    wram_call (backtrack_spec (w := w) φ N T t _ hs' hfit) framed with v₂ m₂ hz₂
    rw [hstep]
    cases hb : Trail.backtrack t <;> rw [hb] at hz₂ <;> exact ⟨by simp only; omega, hz₂.1⟩
  · rw [Bool.not_eq_true] at hc
    rw [hc, Bool.toNat_false] at hconf
    by_cases ha : (φ.all fun c => c.any (Holds π)) = true
    · have hstep := Trail.step_of_status_eq_sat (status_eq_sat hc ha)
      rw [ha, Bool.toNat_true] at halls
      wram_exec [hconf, halls, h1]
      wram_call (outSat_spec (w := w) φ N T t _ hs' hfit) framed with v₂ m₂ hz₂
      rw [hstep]
      exact ⟨by simp only; omega, hz₂⟩
    · rw [Bool.not_eq_true] at ha
      rw [ha, Bool.toNat_false] at halls
      have hstat := status_eq_branch hc ha
      have hstep := Trail.step_of_status_eq_branch hstat
      obtain ⟨hv, hun⟩ := assigned_of_status_eq_branch hstat
      have hcode := branchCode_eq φ π huf hunit hov
      wram_exec [hconf, halls, h1]
      wram_call (push_spec (w := w) φ N T _ t _ hs' (by wram_simp; exact hcode) hv hun hfit) framed
        with v₂ m₂ hz₂
      rw [hstep]
      exact ⟨by simp only; omega, hz₂.1⟩

end Specs

end Cslib.Algorithms.WordRAM.DPLL

end
