/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Scan
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# The DPLL solver on the word RAM: the last-occurrence pass and the steps

This file proves what the last-occurrence pass of the word-RAM DPLL solver writes
(`Cslib.Algorithms.WordRAM.DPLL.lastPass_spec`), and that one iteration of its main loop performs
one step of the search with an explicit trail (`Cslib.Algorithms.WordRAM.DPLL.stepBody_spec`):
the memory holds the trail as a literal array and as a stack of entries
(`Cslib.Algorithms.WordRAM.DPLL.StateAt`), and the step either moves to the memory of the next
trail or writes the output.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Algorithms.WordRAM.ClauseCode Cslib.Algorithms.Lean.DPLL Reg

/-! ### The last-occurrence pass -/

/-- Writing the address of each occurrence into the cell of its variable from `B`. -/
def writeLast (mem : ℕ → ℕ) (B : ℕ) (os : List (ℕ × Literal ℕ)) : ℕ → ℕ :=
  os.foldl (fun m e => Function.update m (B + occVar e) e.1) mem

theorem writeLast_append (mem : ℕ → ℕ) (B : ℕ) (os os' : List (ℕ × Literal ℕ)) :
    writeLast mem B (os ++ os') = writeLast (writeLast mem B os) B os' := by
  simp [writeLast, List.foldl_append]

/-- The cell of a variable after the writes holds its last occurrence. -/
theorem writeLast_cell (mem : ℕ → ℕ) (B : ℕ) (os : List (ℕ × Literal ℕ)) (v : ℕ) :
    writeLast mem B os (B + v) = lastFrom (mem (B + v)) os v := by
  induction os generalizing mem with
  | nil => rfl
  | cons e os ih =>
    simp only [writeLast, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [lastFrom, List.foldl_cons]
    congr 1
    by_cases h : occVar e = v
    · subst h; simp
    · rw [Function.update_of_ne (by omega)]; simp [h]

/-- The writes change no cell below `B`. -/
theorem writeLast_of_lt (mem : ℕ → ℕ) (B : ℕ) (os : List (ℕ × Literal ℕ)) {q : ℕ}
    (hq : q < B) : writeLast mem B os q = mem q := by
  induction os generalizing mem with
  | nil => rfl
  | cons e os ih =>
    simp only [writeLast, List.foldl_cons] at ih ⊢
    rw [ih, Function.update_of_ne (by omega)]

/-- The writes change no cell at `B + N` or above when every variable is below `N`. -/
theorem writeLast_of_ge (mem : ℕ → ℕ) (B N : ℕ) (os : List (ℕ × Literal ℕ))
    (hN : ∀ e ∈ os, occVar e < N) {q : ℕ} (hq : B + N ≤ q) : writeLast mem B os q = mem q := by
  induction os generalizing mem with
  | nil => rfl
  | cons e os ih =>
    simp only [writeLast, List.foldl_cons] at ih ⊢
    have := hN e (by simp)
    rw [ih _ (fun e' he' => hN e' (by simp [he'])), Function.update_of_ne (by omega)]

/-! ### The scan reads the last occurrences -/

theorem openFold_congr (π : List (Literal ℕ)) {f g : ℕ → ℕ} (o : Option ℕ)
    (os : List (ℕ × Literal ℕ)) (h : ∀ e ∈ os, f (occVar e) = g (occVar e)) :
    openFold π f o os = openFold π g o os := by
  induction os generalizing o with
  | nil => rfl
  | cons e os ih =>
    obtain ⟨p, l⟩ := e
    simp only [openFold, List.foldl_cons] at ih ⊢
    have hl : f l.1 = g l.1 := by simpa using h (p, l) (by simp)
    rw [show openLit π f o p l = openLit π g o p l by simp only [openLit, hl]]
    exact ih _ fun e' he' => h e' (by simp [he'])

theorem mem_vars_of_mem_occs {φ : CNF ℕ} {a : ℕ} {e : ℕ × Literal ℕ} (he : e ∈ occs φ a) :
    occVar e ∈ φ.vars := by
  rw [← map_occs φ a]
  exact List.mem_map_of_mem he

/-- The scan depends on the last-occurrence cells only at the variables of the formula. -/
theorem formulaScan_congr (π : List (Literal ℕ)) {f g : ℕ → ℕ} (s : ScanRegs) (a : ℕ)
    (φ : CNF ℕ) (h : ∀ v ∈ φ.vars, f v = g v) :
    formulaScan π f s a φ = formulaScan π g s a φ := by
  rw [formulaScan_eq, formulaScan_eq,
    openFold_congr π _ _ fun e he => h _ (mem_vars_of_mem_occs he)]

theorem length_vars_le (φ : CNF ℕ) : φ.vars.length ≤ (φ.flatMap encodeClause).length := by
  induction φ with
  | nil => simp [CNF.vars]
  | cons c φ ih =>
    simp only [CNF.vars, List.flatten_cons, List.map_append, List.length_append,
      List.length_map, List.flatMap_cons, length_encodeClauseBy] at ih ⊢
    omega

section Specs

variable {w : ℕ}

/-- **The literal loop of the pass** writes the addresses of the literals at `lptr`. -/
theorem lastLits_spec (ls : Clause ℕ) (x : Data 32) (N : ℕ)
    (hone : x.regs one = 1) (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hend : x.regs lend = x.regs lptr + ls.length) (hN : ∀ l ∈ ls, l.1 < N)
    (hlb : x.regs lend ≤ x.regs lb) (hfitB : Fits w (x.regs lb + N))
    (hfit2 : Fits w (2 * N)) :
    ∃ y, ExecWithin w (.loop (.lt lptr lend) lastLit) x y (7 * ls.length + 2) ∧
      y.mem = writeLast x.mem (x.regs lb) (litOccs (x.regs lptr) ls) ∧
      y.regs lptr = x.regs lend ∧ y.regs lb = x.regs lb ∧ y.regs lend = x.regs lend ∧
      y.regs cend = x.regs cend ∧ y.regs one = x.regs one := by
  induction ls generalizing x with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), rfl, by simp [hend], rfl, rfl, rfl, rfl⟩
    simp [Cond.holds_lt, hend]
  | cons l ls ih =>
    simp only [List.length_cons] at hend
    have hc : (Cond.lt lptr lend).Holds x := by simp only [Cond.holds_lt, hend]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp (by simpa using hl)
    have hlN := hN l (by simp)
    have hshr : litCode l >>> 1 = l.1 := litCodeBy_shiftRight _root_.id l
    have : Fits w (litCode l) := hfit2.of_le (litCode_lt hlN).le
    have : Fits w l.1 := hfitB.of_le (by omega)
    have : Fits w (x.regs lb + l.1) := hfitB.of_le (by omega)
    have : Fits w (x.regs lptr + 1) := hfitB.of_le (by omega)
    have : Fits w 1 := hfitB.of_le (by omega)
    obtain ⟨y, hy, hym, hyp, hylb, hyle, hy1⟩ : ∃ y, ExecWithin w lastLit x y 5 ∧
        y.mem = Function.update x.mem (x.regs lb + l.1) (x.regs lptr) ∧
        y.regs lptr = x.regs lptr + 1 ∧ y.regs lb = x.regs lb ∧ y.regs lend = x.regs lend ∧
        y.regs one = 1 := by
      refine WP.exists_execWithin ?_
      unfold lastLit
      wram_exec [hlit, hone, hshr]
      wram_simp [hone]
    have hfr : HoldsList (y.regs lptr) (ls.map litCode) y.mem := by
      rw [hym, hyp]
      refine hrest.frame fun a h₁ h₂ => ?_
      rw [Function.update_of_ne]
      simp only [List.length_map] at h₁ h₂
      omega
    obtain ⟨z, hz, hzm, hzp, -, -, -, -⟩ := ih y hy1 hfr (by rw [hyle, hyp, hend]; omega)
      (fun l' hl' => hN l' (by simp [hl'])) (by rw [hyle, hylb]; exact hlb)
      (by rw [hylb]; exact hfitB)
    have hall := ExecWithin.loop_iter hc hy hz
    refine ⟨z, hall.mono (by simp only [List.length_cons]; omega),
      ?_, by rw [hzp, hyle], hall.regs_eq (by decide), hall.regs_eq (by decide),
      hall.regs_eq (by decide), hall.regs_eq (by decide)⟩
    rw [hzm, hym, hylb, hyp]
    rfl

/-- **The clause loop of the pass** writes the addresses of the literals of the clauses from
`ptr` to `cend`. -/
theorem lastClauses_spec (ψ : CNF ℕ) (x : Data 32) (N : ℕ)
    (hone : x.regs one = 1) (hcl : HoldsList (x.regs ptr) (ψ.flatMap encodeClause) x.mem)
    (hend : x.regs ptr + (ψ.flatMap encodeClause).length = x.regs cend)
    (hN : ∀ c ∈ ψ, ∀ l ∈ c, l.1 < N) (hlb : x.regs cend ≤ x.regs lb)
    (hfitB : Fits w (x.regs lb + N)) (hfit2 : Fits w (2 * N)) :
    ∃ y, ExecWithin w (.loop (.lt ptr cend) lastClause) x y
        (8 * (ψ.flatMap encodeClause).length + 2) ∧
      y.mem = writeLast x.mem (x.regs lb) (occs ψ (x.regs ptr)) := by
  induction ψ generalizing x with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono le_rfl, rfl⟩
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero] at hend
    simp [Cond.holds_lt, hend]
  | cons c ψ ih =>
    simp only [List.flatMap_cons] at hcl hend
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hcl
    simp only [List.length_append, length_encodeClauseBy] at hend hpψ
    obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp hpc
    have hc : (Cond.lt ptr cend).Holds x := by simp only [Cond.holds_lt]; omega
    have : Fits w (x.regs ptr + 1) := hfitB.of_le (by omega)
    have : Fits w (x.regs ptr + 1 + c.length) := hfitB.of_le (by omega)
    obtain ⟨y, hy, hym, hylb, hyce, hy1, hyp⟩ :
        ∃ y, ExecWithin w lastClause x y (7 * c.length + 6) ∧
        y.mem = writeLast x.mem (x.regs lb) (litOccs (x.regs ptr + 1) c) ∧
        y.regs lb = x.regs lb ∧ y.regs cend = x.regs cend ∧ y.regs one = 1 ∧
        y.regs ptr = x.regs ptr + 1 + c.length := by
      refine WP.exists_execWithin ?_
      unfold lastClause
      wram_exec [hlen, hone]
      wram_call (lastLits_spec (w := w) c _ N (by wram_simp [hone]) (by wram_simp; exact hlits)
        (by wram_simp) (hN c (by simp)) (by wram_simp; omega) (by wram_simp; exact hfitB) hfit2)
        with y ⟨hym, hyp, hylb, hyle, hyce, hy1⟩
      wram_exec
      wram_simp at hym hyp hylb hyle hyce hy1 ⊢
      exact ⟨hym, hylb, hyce, hy1.trans hone, hyle⟩
    have hfr : HoldsList (y.regs ptr) (ψ.flatMap encodeClause) y.mem := by
      rw [hym, hyp]
      refine (show x.regs ptr + 1 + c.length = x.regs ptr + (c.length + 1) by omega) ▸ hpψ
        |>.frame fun a h₁ h₂ => writeLast_of_lt _ _ _ (by omega)
    obtain ⟨z, hz, hzm⟩ := ih y hy1 hfr (by rw [hyp, hyce]; omega)
      (fun c' hc' => hN c' (by simp [hc'])) (by rw [hyce, hylb]; exact hlb)
      (by rw [hylb]; exact hfitB)
    refine ⟨z, (ExecWithin.loop_iter hc hy hz).mono ?_, ?_⟩
    · simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]; omega
    · rw [hzm, hym, hylb, hyp, occs, writeLast_append]
      congr 2
      omega

/-- **The last-occurrence pass** writes, for each variable of the clauses from address `2` to
`cend`, the address of its last occurrence into its cell from `lb`. -/
theorem lastPass_spec (φ : CNF ℕ) (x : Data 32) (N : ℕ)
    (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hcl : HoldsList 2 (φ.flatMap encodeClause) x.mem)
    (hend : 2 + (φ.flatMap encodeClause).length = x.regs cend)
    (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) (hlb : x.regs cend ≤ x.regs lb)
    (hfitB : Fits w (x.regs lb + N)) (hfit2 : Fits w (2 * N)) :
    ∃ y, ExecWithin w lastPass x y (8 * (φ.flatMap encodeClause).length + 3) ∧
      y.mem = writeLast x.mem (x.regs lb) (occs φ 2) := by
  refine WP.exists_execWithin ?_
  unfold lastPass
  wram_exec [htwo]
  wram_call (lastClauses_spec (w := w) φ _ N (by wram_simp [hone]) (by wram_simp [htwo]; exact hcl)
    (by wram_simp [htwo]; exact hend) hN (by wram_simp; exact hlb) (by wram_simp; exact hfitB)
    hfit2) with y hym
  refine ⟨by omega, ?_⟩
  wram_simp [htwo] at hym
  exact hym

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

/-- The memory of a trail: the clauses from address `2` to `T`, the literal array at `T`, the
last occurrences at `T + 2 N`, and the trail entries at `T + 3 N`. -/
structure MemAt (φ : CNF ℕ) (N T : ℕ) (mem : ℕ → ℕ) (t : Trail) : Prop where
  clauses : HoldsList 2 (φ.flatMap encodeClause) mem
  hT : 2 + (φ.flatMap encodeClause).length = T
  vars : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N
  lits : LitArr mem T N (Trail.lits t)
  last : ∀ v < N, mem (T + 2 * N + v) = lastPos (occs φ 2) v
  trail : HoldsList (T + 3 * N) (trailWords t) mem
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
      else if a = T + 3 * N + 2 * t.length then litCode l
      else if a = T + 3 * N + 2 * t.length + 1 then b.toNat
      else mem a) :
    MemAt φ N T mem' (⟨l, b⟩ :: t) := by
  have hlN := mem_vars_lt h hl
  have hc := litCode_lt hlN
  have hT := h.hT
  -- Cells away from the three written ones keep their contents.
  have hframe : ∀ a, a ≠ T + litCode l → a ≠ T + 3 * N + 2 * t.length →
      a ≠ T + 3 * N + 2 * t.length + 1 → mem' a = mem a := fun a h₁ h₂ h₃ => by
    simp [hmem, h₁, h₂, h₃]
  refine ⟨h.clauses.frame fun a _ ha' => hframe a (by omega) (by omega) (by omega), h.hT,
    h.vars, fun l' hl' => ?_, fun v hv => ?_, ?_, ?_⟩
  · have hc' := litCode_lt hl'
    by_cases he : l' = l
    · subst he; simp [hmem, Trail.lits]
    · have hne : T + litCode l' ≠ T + litCode l := fun h' =>
        he (litCodeBy_injective Function.injective_id (show litCode l' = litCode l by omega))
      rw [hframe _ hne (by omega) (by omega), h.lits l' hl']
      simp [Trail.lits, he]
  · rw [hframe _ (by omega) (by omega) (by omega)]; exact h.last v hv
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
      (T + 3 * N + 2 * t.length) (litCode l)) (T + 3 * N + 2 * t.length + 1) 0)
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
  refine ⟨h.clauses.frame fun a _ ha' => ?_, h.hT, h.vars, ?_, fun v hv => ?_, ?_, h.ok.tail⟩
  · rw [Function.update_of_ne (by omega)]
  · refine LitArr.update h.lits l 0 (by simp [hnot]) fun l' hl' => ?_
    simp [Trail.lits, hl']
  · rw [Function.update_of_ne (by omega)]; exact h.last v hv
  · exact htr.frame fun a h₁ _ => by rw [Function.update_of_ne (by omega)]

/-- **Flipping a first branch** into the second branch: popping it, then pushing its negation as
a second branch. -/
theorem MemAt.flip {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {l : Literal ℕ} {t : Trail}
    (h : MemAt φ N T mem (⟨l, false⟩ :: t)) :
    MemAt φ N T (Function.update (Function.update (Function.update (Function.update mem
      (T + litCode l) 0) (T + litCode l.negate) 1) (T + 3 * N + 2 * t.length)
      (litCode l.negate)) (T + 3 * N + 2 * t.length + 1) 1) (⟨l.negate, true⟩ :: t) := by
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

/-- **The state at the head of the main loop** for the trail `t`. -/
structure StateAt (φ : CNF ℕ) (N T : ℕ) (x : Data 32) (t : Trail) : Prop where
  zero : x.regs zero = 0
  one : x.regs one = 1
  two : x.regs two = 2
  tb : x.regs tb = T
  cend : x.regs cend = T
  lb : x.regs lb = T + 2 * N
  sb : x.regs sb = T + 3 * N
  ob : x.regs ob = T + 5 * N
  nv : x.regs nv = N
  go : x.regs go = 1
  tp : x.regs tp = T + 3 * N + 2 * t.length
  mem : MemAt φ N T x.mem t

/-- Setting a register outside the state keeps the state. -/
theorem StateAt.set {φ : CNF ℕ} {N T : ℕ} {x : Data 32} {t : Trail} (h : StateAt φ N T x t)
    (r : Fin 32) (v : ℕ)
    (hr : r ∉ ({Reg.zero, Reg.one, Reg.two, Reg.tb, Reg.cend, Reg.lb, Reg.sb, Reg.ob, Reg.nv,
      Reg.go, Reg.tp} : Finset (Fin 32))) :
    StateAt φ N T (x.set r v) t := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  exact ⟨by rw [Data.set_regs, Function.update_of_ne (Ne.symm h0)]; exact h.zero,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h1)]; exact h.one,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h2)]; exact h.two,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h3)]; exact h.tb,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h4)]; exact h.cend,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h5)]; exact h.lb,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h6)]; exact h.sb,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h7)]; exact h.ob,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h8)]; exact h.nv,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h9)]; exact h.go,
    by rw [Data.set_regs, Function.update_of_ne (Ne.symm h10)]; exact h.tp, h.mem⟩

/-- **Branching** pushes the literal `l` given by the scan registers. -/
theorem push_spec (φ : CNF ℕ) (N T : ℕ) (x : Data 32) (t : Trail) (l : Literal ℕ)
    (hs : StateAt φ N T x t)
    (hcode : (if x.regs uf = 0 then x.regs ov + x.regs ov + 1 else x.regs unit) = litCode l)
    (hl : l.1 ∈ φ.vars) (ha : Assigned (Trail.lits t) l.1 = false)
    (hfit : Fits w (T + 6 * N + 2)) :
    ∃ y, ExecWithin w push x y 12 ∧ StateAt φ N T y (⟨l, false⟩ :: t) := by
  have hpush := hs.mem.push hl ha
  have hlen := hpush.ok.length_le (fun v hv => mem_vars_lt hs.mem hv)
  simp only [List.length_cons] at hlen
  have hlN := mem_vars_lt hs.mem hl
  have hc := litCode_lt hlN
  have : Fits w (T + 3 * N + 2 * t.length + 1) := hfit.of_le (by omega)
  have : Fits w (T + 3 * N + 2 * t.length + 2) := hfit.of_le (by omega)
  have : Fits w (T + litCode l) := hfit.of_le (by omega)
  have : Fits w (litCode l) := hfit.of_le (by omega)
  have : Fits w (litCode l - 1) := hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold push
  by_cases hu : x.regs uf = 0
  · simp only [hu, ↓reduceIte] at hcode
    have : Fits w (x.regs ov + x.regs ov) := hfit.of_le (by omega)
    wram_exec [hu, hs.zero, hs.one, hs.two, hs.tp, hs.tb, hcode]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp [hs.zero, hs.one, hs.two, hs.tb, hs.cend, hs.lb, hs.sb, hs.ob, hs.nv, hs.go]
    · simp only [List.length_cons]; omega
    · exact hpush
  · simp only [hu, ↓reduceIte] at hcode
    wram_exec [hu, hs.zero, hs.one, hs.two, hs.tp, hs.tb, hcode]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp [hs.zero, hs.one, hs.two, hs.tb, hs.cend, hs.lb, hs.sb, hs.ob, hs.nv, hs.go]
    · simp only [List.length_cons]; omega
    · exact hpush

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
    mem (T + 3 * N + 2 * t.length) = litCode l ∧
      mem (T + 3 * N + 2 * t.length + 1) = b.toNat := by
  have := (holdsList_append_iff.mp (trailWords_cons ⟨l, b⟩ t ▸ h.trail)).2
  rw [length_trailWords] at this
  obtain ⟨h₁, h₂⟩ := holdsList_cons_iff.mp this
  exact ⟨h₁, (holdsList_cons_iff.mp h₂).1⟩

/-- **The pop loop** drops the second branches on top of the trail. -/
theorem popLoop_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (haux : x.regs aux = 1) (hfit : Fits w (T + 6 * N + 2)) :
    ∃ y, ExecWithin w popLoop x y (14 * t.length + 14) ∧ StateAt φ N T y (dropSecond t) ∧
      y.regs aux = 0 := by
  have hlen := hs.mem.ok.length_le (fun v hv => mem_vars_lt hs.mem hv)
  have hc : (Cond.eq aux one).Holds x := by simp [Cond.holds_eq, haux, hs.one]
  induction t generalizing x with
  | nil =>
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold popBody
    have hst : ¬ x.regs sb < x.regs tp := by rw [hs.sb, hs.tp]; simp
    wram_exec [hst]
    refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_eq, hs.one, hs.zero]))
      ⟨by simp, hs.set aux _ (by decide), by wram_simp [hs.zero]⟩
  | cons e t ih =>
    obtain ⟨l, b⟩ := e
    simp only [List.length_cons] at hlen
    have htp : x.regs tp = T + 3 * N + 2 * t.length + 2 := by rw [hs.tp]; simp; omega
    have hst : x.regs sb < x.regs tp := by rw [hs.sb, htp]; omega
    obtain ⟨hcode, hflag⟩ := hs.mem.top
    have hlN : l.1 < N := mem_vars_lt hs.mem (hs.mem.ok.2 ⟨l, b⟩ List.mem_cons_self)
    have hcl := litCode_lt hlN
    have : Fits w (T + 3 * N + 2 * t.length + 1) := hfit.of_le (by omega)
    have : Fits w (T + 3 * N + 2 * t.length) := hfit.of_le (by omega)
    have : Fits w (T + litCode l) := hfit.of_le (by omega)
    have : Fits w 1 := hfit.of_le (by omega)
    have : Fits w 2 := hfit.of_le (by omega)
    have h1 : T + 3 * N + 2 * t.length + 2 - 1 = T + 3 * N + 2 * t.length + 1 := by omega
    have h2 : T + 3 * N + 2 * t.length + 2 - 2 = T + 3 * N + 2 * t.length := by omega
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold popBody
    cases b
    · simp only [Bool.toNat_false] at hflag
      wram_exec [hst, htp, hs.one, hs.two, hs.zero, h1, h2, hflag]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_eq, hs.one, hs.zero]))
        ⟨by simp only [List.length_cons]; omega, ?_, by wram_simp [hs.zero]⟩
      rw [dropSecond_cons_false]
      exact ((hs.set addr _ (by decide)).set addr _ (by decide)).set aux _ (by decide)
    · simp only [Bool.toNat_true] at hflag
      wram_exec [hst, htp, hs.one, hs.two, hs.zero, h1, h2, hflag, hcode, hs.tb]
      wram_call (ih _ (by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            wram_simp [hs.zero, hs.one, hs.two, hs.tb, hs.cend, hs.lb, hs.sb, hs.ob, hs.nv, hs.go]
          exact hs.mem.pop)
        (by wram_simp [haux]) (by omega) (by wram_simp [Cond.holds_eq, haux, hs.one]))
        with y ⟨hy, hya⟩
      exact ⟨by simp only [List.length_cons]; omega, by rw [dropSecond_cons_true]; exact hy, hya⟩

/-- **Backtracking**: the state of the backtracked trail, or the output `[0]` at `T + 5 N`. -/
theorem backtrack_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (hfit : Fits w (T + 6 * N + 2)) :
    ∃ y, ExecWithin w backtrack x y (14 * t.length + 40) ∧
      match Trail.backtrack t with
      | some t' => StateAt φ N T y t'
      | none => y.regs go = 0 ∧ y.regs out = T + 5 * N ∧
          outputList y.mem (T + 5 * N) = [0] := by
  have : Fits w (T + 5 * N + 1) := hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold backtrack
  wram_exec [hs.one]
  wram_call (popLoop_spec (w := w) φ N T t _ (hs.set aux _ (by decide)) (by wram_simp [hs.one])
    hfit) with y ⟨hy, hya⟩
  have hdl := length_dropSecond_le t
  rw [backtrack_eq]
  cases hd : dropSecond t with
  | nil =>
    rw [hd] at hy
    have hst : ¬ y.regs sb < y.regs tp := by rw [hy.sb, hy.tp]; simp
    unfold outUnsat
    wram_exec [hst, hy.ob, hy.one, hy.zero]
    refine ⟨by wram_simp [hy.zero], by wram_simp [hy.ob], ?_⟩
    rw [outputList_eq_iff]
    wram_simp
    refine ⟨by simp, holdsList_cons_iff.mpr ⟨by simp, fun i => i.elim0⟩⟩
  | cons e t' =>
    obtain ⟨l, b⟩ := e
    obtain rfl := dropSecond_eq_cons hd
    rw [hd] at hy hdl
    simp only [List.length_cons] at hdl
    have hlen := hy.mem.ok.length_le (fun v hv => mem_vars_lt hy.mem hv)
    simp only [List.length_cons] at hlen
    have htp : y.regs tp = T + 3 * N + 2 * t'.length + 2 := by rw [hy.tp]; simp; omega
    have hst : y.regs sb < y.regs tp := by rw [hy.sb, htp]; omega
    obtain ⟨hcode, -⟩ := hy.mem.top
    have hlN : l.1 < N := mem_vars_lt hy.mem (hy.mem.ok.2 ⟨l, false⟩ List.mem_cons_self)
    have hcl := litCode_lt hlN
    have hncl := litCode_lt (l := l.negate) hlN
    have hxor : litCode l ^^^ 1 = litCode l.negate := litCodeBy_xor_one _root_.id l
    have h2 : T + 3 * N + 2 * t'.length + 2 - 2 = T + 3 * N + 2 * t'.length := by omega
    have : Fits w (T + 3 * N + 2 * t'.length) := hfit.of_le (by omega)
    have : Fits w (T + 3 * N + 2 * t'.length + 1) := hfit.of_le (by omega)
    have : Fits w (T + litCode l) := hfit.of_le (by omega)
    have : Fits w (T + litCode l.negate) := hfit.of_le (by omega)
    have : Fits w (litCode l.negate) := hfit.of_le (by omega)
    wram_exec [hst, htp, h2, hcode, hy.tb, hy.zero, hy.one, hy.two, hxor]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp [hy.zero, hy.one, hy.two, hy.tb, hy.cend, hy.lb, hy.sb, hy.ob, hy.nv, hy.go]
    · omega
    · exact hy.mem.flip

theorem litCode_true (v : ℕ) : litCode (v, true) = v + v + 1 := by
  simp [litCodeBy]; omega

/-- **The model loop** writes the bits of the true literals of `π` for the variables from `var`
to `N` at `T + 5 N + 2`. -/
theorem outLoop_spec (π : List (Literal ℕ)) (N T k : ℕ) (x : Data 32)
    (hone : x.regs one = 1) (htwo : x.regs two = 2) (htb : x.regs tb = T)
    (hob : x.regs ob = T + 5 * N) (hnv : x.regs nv = N) (hvar : x.regs var + k = N)
    (hπ : LitArr x.mem T N π) (hfit : Fits w (T + 6 * N + 2)) :
    ∃ y, ExecWithin w (.loop (.lt var nv) outBody) x y (10 * k + 2) ∧
      (∀ i, x.regs var ≤ i → i < N → y.mem (T + 5 * N + 2 + i) = (π.contains (i, true)).toNat) ∧
      (∀ a, a < T + 5 * N + 2 + x.regs var → y.mem a = x.mem a) ∧
      y.regs ob = x.regs ob ∧ y.regs zero = x.regs zero := by
  induction k generalizing x with
  | zero =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), fun i h₁ h₂ => by omega,
      fun _ _ => rfl, rfl, rfl⟩
    simp [Cond.holds_lt, hnv]; omega
  | succ k ih =>
    have hc : (Cond.lt var nv).Holds x := by simp only [Cond.holds_lt, hnv]; omega
    have hvN : x.regs var < N := by omega
    have hlit := hπ (x.regs var, true) hvN
    rw [litCode_true] at hlit
    have : Fits w (x.regs var + x.regs var + 1) := hfit.of_le (by omega)
    have : Fits w (x.regs var + x.regs var) := hfit.of_le (by omega)
    have : Fits w (T + (x.regs var + x.regs var + 1)) := hfit.of_le (by omega)
    have : Fits w (T + 5 * N + x.regs var) := hfit.of_le (by omega)
    have : Fits w (T + 5 * N + x.regs var + 2) := hfit.of_le (by omega)
    have : Fits w (x.regs var + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold outBody
    wram_exec [hone, htwo, htb, hob, hlit]
    wram_call (ih _ (by wram_simp [hone]) (by wram_simp [htwo]) (by wram_simp [htb])
      (by wram_simp [hob]) (by wram_simp [hnv]) (by wram_simp; omega)
      (by wram_simp; exact hπ.update_ge (by omega) _)) with y ⟨hy₁, hy₂, hyo, hyz⟩
    refine ⟨by omega, fun i h₁ h₂ => ?_, fun a ha => ?_, by wram_simp at hyo; exact hyo,
      by wram_simp at hyz; exact hyz⟩
    · wram_simp at hy₁ hy₂
      rcases Nat.lt_or_ge (x.regs var) i with hi | hi
      · exact hy₁ i (by omega) h₂
      · obtain rfl : i = x.regs var := by omega
        rw [hy₂ _ (by omega)]
        simp [show T + 5 * N + 2 + x.regs var = T + 5 * N + x.regs var + 2 by omega]
    · wram_simp at hy₂
      rw [hy₂ _ (by omega)]
      wram_simp

/-- The output of a model: `1`, then the bits of the true literals of `π` below `N`. -/
def modelWords (N : ℕ) (π : List (Literal ℕ)) : List ℕ :=
  1 :: (List.range N).map fun v => (assignment π v).toNat

/-- **Writing the model** of the trail at `T + 5 N`. -/
theorem outSat_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (hfit : Fits w (T + 6 * N + 2)) :
    ∃ y, ExecWithin w outSat x y (10 * N + 10) ∧ y.regs go = 0 ∧ y.regs out = T + 5 * N ∧
      outputList y.mem (T + 5 * N) = modelWords N (Trail.lits t) := by
  have : Fits w (N + 1) := hfit.of_le (by omega)
  have : Fits w (T + 5 * N + 1) := hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold outSat
  wram_exec [hs.nv, hs.one, hs.ob, hs.zero]
  wram_call (outLoop_spec (w := w) (Trail.lits t) N T N _ (by wram_simp [hs.one])
    (by wram_simp [hs.two]) (by wram_simp [hs.tb]) (by wram_simp [hs.ob]) (by wram_simp [hs.nv])
    (by wram_simp)
    (by wram_simp; exact (hs.mem.lits.update_ge (by omega) _).update_ge (by omega) _) hfit)
    with y ⟨hy₁, hy₂, hyo, hyz⟩
  wram_simp at hy₁ hy₂ hyo hyz
  wram_exec [hyo, hyz, hs.ob, hs.zero]
  refine ⟨by wram_simp, by wram_simp, ?_⟩
  wram_simp
  rw [outputList_eq_iff]
  refine ⟨?_, holdsList_cons_iff.mpr ⟨?_, fun i => ?_⟩⟩
  · rw [hy₂ _ (by omega)]; simp [modelWords]
  · rw [hy₂ _ (by omega)]; simp
  · have hi : i.val < N := by simpa [modelWords] using i.isLt
    change y.mem (T + 5 * N + 1 + 1 + i.val) = _
    rw [show T + 5 * N + 1 + 1 + i.val = T + 5 * N + 2 + i.val by omega, hy₁ i.val (by omega) hi]
    have hget : ((List.range N).map fun v => (assignment (Trail.lits t) v).toNat)[i.val]'
        (by simpa using hi) = (assignment (Trail.lits t) i.val).toNat := by simp
    exact (hget.trans (by simp [assignment])).symm

/-- The output for an answer of the search. -/
def answerList (N : ℕ) : Trail.Answer → List ℕ
  | .sat π => modelWords N π
  | .unsat => [0]

/-- The instructions of one step: a pass over the clauses, then backtracking, branching, or
writing the model. -/
def stepTime (φ : CNF ℕ) (N : ℕ) (t : Trail) : ℕ :=
  32 * (φ.flatMap encodeClause).length + 14 * t.length + 60 +
    match Trail.step φ t with
    | .inr _ => 0
    | .inl _ => 10 * N

theorem StateAt.preserve {φ : CNF ℕ} {N T : ℕ} {x y : Data 32} {t : Trail} {c : Code .standard 32}
    {n : ℕ} (h : StateAt φ N T x t) (hy : ExecWithin w c x y n) (hm : y.mem = x.mem)
    (hr : ∀ r ∈ ({Reg.zero, Reg.one, Reg.two, Reg.tb, Reg.cend, Reg.lb, Reg.sb, Reg.ob, Reg.nv,
      Reg.go, Reg.tp} : Finset (Fin 32)), c.Preserves r) : StateAt φ N T y t :=
  ⟨by rw [hy.regs_eq (hr _ (by decide))]; exact h.zero,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.one,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.two,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.tb,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.cend,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.lb,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.sb,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.ob,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.nv,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.go,
    by rw [hy.regs_eq (hr _ (by decide))]; exact h.tp, hm ▸ h.mem⟩

/-- **One step of the search** on the word RAM: the state of the next trail, or the output of the
answer at `T + 5 N`. -/
theorem stepBody_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (x : Data 32) (hs : StateAt φ N T x t)
    (hfit : Fits w (T + 6 * N + 2)) :
    ∃ y, ExecWithin w stepBody x y (stepTime φ N t) ∧
      match Trail.step φ t with
      | .inr t' => StateAt φ N T y t'
      | .inl a => y.regs go = 0 ∧ y.regs out = T + 5 * N ∧
          outputList y.mem (T + 5 * N) = answerList N a := by
  set π := Trail.lits t
  have hT := hs.mem.hT
  have hlast : ∀ v ∈ φ.vars, x.mem (x.regs lb + v) = lastPos (occs φ 2) v := fun v hv => by
    rw [hs.lb]; exact hs.mem.last v (mem_vars_lt hs.mem hv)
  have hlenL : t.length ≤ (φ.flatMap encodeClause).length :=
    hs.mem.ok.length_le_vars.trans (length_vars_le φ)
  have hscan : ∃ y, ExecWithin w scan x y (32 * (φ.flatMap encodeClause).length + 9) ∧
      StateAt φ N T y t ∧ ScanAt y ⟨φ.any (Falsifies π), φ.all (fun c => c.any (Holds π)),
        (unitLiteral? φ π).map litCode, φ.vars.dedup.find? fun x => !Assigned π x⟩ := by
    obtain ⟨y, hy, hym, hys⟩ := scan_spec (w := w) π φ x N hs.zero hs.one hs.two
      hs.mem.clauses (by rw [hs.cend]; exact hT) hs.mem.vars (by rw [hs.tb]; exact hs.mem.lits)
      (by rw [hs.tb]; exact hfit.of_le (by omega)) (by rw [hs.lb]; exact hfit.of_le (by omega))
      (by rw [hs.cend]; exact hfit.of_le (by omega))
    rw [formulaScan_congr π _ _ φ hlast, formulaScan_init] at hys
    exact ⟨y, hy, hs.preserve hy hym (by decide), hys⟩
  refine WP.exists_execWithin ?_
  unfold stepBody
  refine WP.seq ?_
  obtain ⟨y, hy, hsy, hconf, halls, huf, hunit, hopf, hov⟩ := hscan
  refine WP.of_execWithin hy ?_
  simp only at hconf halls huf hunit hopf hov
  by_cases hc : φ.any (Falsifies π) = true
  · have hstat : status φ π = .conflict := by
      unfold status; rw [List.isSome_find?, hc]; rfl
    rw [hc, Bool.toNat_true] at hconf
    have hstep : Trail.step φ t = match Trail.backtrack t with
        | none => .inl .unsat
        | some t' => .inr t' := by
      unfold Trail.step; rw [show Trail.lits t = π from rfl, hstat]
      rfl
    wram_exec [hconf, hsy.one]
    wram_call (backtrack_spec (w := w) φ N T t _ hsy hfit) with z hz
    unfold stepTime
    rw [hstep]
    cases hb : Trail.backtrack t with
    | none =>
      rw [hb] at hz
      exact ⟨by omega, hz⟩
    | some t' =>
      rw [hb] at hz
      exact ⟨by omega, hz⟩
  · rw [Bool.not_eq_true] at hc
    rw [hc, Bool.toNat_false] at hconf
    have hc0 : ¬ (0 : ℕ) = 1 := by omega
    by_cases ha : (φ.all fun c => c.any (Holds π)) = true
    · have hstat : status φ π = .sat := by
        unfold status; rw [List.isSome_find?, hc]; simp only [Bool.false_eq_true, ↓reduceIte, ha]
      have hstep : Trail.step φ t = .inl (.sat π) := by
        unfold Trail.step; rw [show Trail.lits t = π from rfl, hstat]
      rw [ha, Bool.toNat_true] at halls
      wram_exec [hconf, halls, hsy.one, hc0]
      wram_call (outSat_spec (w := w) φ N T t _ hsy hfit) with z ⟨hz₁, hz₂, hz₃⟩
      unfold stepTime
      rw [hstep]
      exact ⟨by simp only; omega, hz₁, hz₂, hz₃⟩
    · rw [Bool.not_eq_true] at ha
      rw [ha, Bool.toNat_false] at halls
      have hstat : status φ π = .branch (nextLiteral φ π) := by
        unfold status; rw [List.isSome_find?, hc]; simp only [Bool.false_eq_true, ↓reduceIte, ha]
      have hstep : Trail.step φ t = .inr (⟨nextLiteral φ π, false⟩ :: t) := by
        unfold Trail.step; rw [show Trail.lits t = π from rfl, hstat]
      obtain ⟨hv, hun⟩ := assigned_of_status_eq_branch hstat
      have hcode : (if y.regs uf = 0 then y.regs ov + y.regs ov + 1 else y.regs unit) =
          litCode (nextLiteral φ π) := by
        rw [huf, hunit, hov]
        unfold nextLiteral
        cases hu : unitLiteral? φ π with
        | some l => simp
        | none => simp [litCode_true]
      wram_exec [hconf, halls, hsy.one, hsy.zero, hc0]
      wram_call (push_spec (w := w) φ N T _ t _ hsy hcode hv hun hfit) with z hz
      unfold stepTime
      rw [hstep]
      exact ⟨by simp only; omega, hz⟩

end Specs

end Cslib.Algorithms.WordRAM.DPLL

end
