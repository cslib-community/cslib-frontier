/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop

/-!
# The DPLL solver on the word RAM: what the scan computes

The scan of the word-RAM DPLL solver (`Cslib.Algorithms.WordRAM.DPLL.scan`) makes one pass over the
clauses. This file states what it computes as a fold over the clauses and their literals
(`Cslib.Algorithms.WordRAM.DPLL.clauseStep`, `Cslib.Algorithms.WordRAM.DPLL.litStep`), proves that
the fold gives the status of the trail (`Cslib.Algorithms.Lean.DPLL.status`): a falsified clause,
satisfaction, the literal of the first unit clause, and the variable of the first literal
occurrence that is open (`Cslib.Algorithms.WordRAM.DPLL.foldl_clauseStep_init`), and proves that
the program computes the fold (`Cslib.Algorithms.WordRAM.DPLL.scan_spec`).

## Main definitions

* `Cslib.Algorithms.WordRAM.DPLL.litStep`, `Cslib.Algorithms.WordRAM.DPLL.clauseStep`: one literal
  and one clause of the scan.
* `Cslib.Algorithms.WordRAM.DPLL.LitArr`: the literal array holds a partial assignment.

## Main results

* `Cslib.Algorithms.WordRAM.DPLL.foldl_clauseStep_init`: the fold computes the status.
* `Cslib.Algorithms.WordRAM.DPLL.scan_spec`: the scan computes the status within `23 E + 9`
  instructions, where `E` is the number of words of the clauses, and leaves memory unchanged.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Algorithms.WordRAM.ClauseCode
open Cslib.Algorithms.Lean.DPLL

/-! ### The fold of the scan -/

/-- The registers of the literal loop: the number of literals of the current clause not falsified
so far, the code of the last of them, whether one of them is true, and the first open variable. -/
structure LitRegs where
  /-- The number of literals not falsified so far. -/
  cnt : ℕ
  /-- The code of the last such literal. -/
  uc : ℕ
  /-- Whether a true literal was found. -/
  sat : Bool
  /-- The first open variable. -/
  opened : Option ℕ
  deriving DecidableEq, Repr

/-- One literal against the partial assignment `π`: a falsified literal changes nothing; a true
one is counted and recorded; the variable of any other is open, and is recorded when it is the
first. -/
def litStep (π : List (Literal ℕ)) (r : LitRegs) (l : Literal ℕ) : LitRegs :=
  if π.contains l.negate then r
  else if π.contains l then ⟨r.cnt + 1, litCode l, true, r.opened⟩
  else ⟨r.cnt + 1, litCode l, r.sat, r.opened.or (some l.1)⟩

/-- Whether some literal of `π` has the code `u`. -/
def codeOn (π : List (Literal ℕ)) (u : ℕ) : Bool := π.any fun l => litCode l == u

/-- The registers of the scan: a falsified clause, whether every clause has a true literal, the
code of the literal of the first unit clause, and the first open variable. -/
structure ScanRegs where
  /-- A falsified clause was found. -/
  conf : Bool
  /-- Every clause so far has a true literal. -/
  alls : Bool
  /-- The code of the literal of the first unit clause not on the trail. -/
  unit : Option ℕ
  /-- The first open variable. -/
  opened : Option ℕ
  deriving DecidableEq, Repr

/-- The registers at the start of the scan. -/
def ScanRegs.init : ScanRegs := ⟨false, true, none, none⟩

/-- The end of a clause whose literal loop ended with the registers `r`. -/
def endClause (π : List (Literal ℕ)) (s : ScanRegs) (r : LitRegs) : ScanRegs :=
  ⟨s.conf || r.cnt == 0, s.alls && r.sat,
    s.unit.or (if r.cnt == 1 && !codeOn π r.uc then some r.uc else none), r.opened⟩

/-- One clause of the scan. -/
def clauseStep (π : List (Literal ℕ)) (s : ScanRegs) (c : Clause ℕ) : ScanRegs :=
  endClause π s (c.foldl (litStep π) ⟨0, 0, false, s.opened⟩)

/-! ### The fold computes the status -/

/-- The literals of a clause not falsified by `π`. -/
abbrev notFalse (π : List (Literal ℕ)) (c : Clause ℕ) : Clause ℕ :=
  c.filter fun l => !π.contains l.negate

/-- Assignment of a variable through the two literals on it. -/
theorem not_assigned_iff (π : List (Literal ℕ)) (l : Literal ℕ) :
    (!π.contains l && !π.contains l.negate) = !Assigned π l.1 := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [Assigned, Std.Sat.Literal.negate, Bool.and_comm]

theorem litStep_cnt_le (π : List (Literal ℕ)) (r : LitRegs) (l : Literal ℕ) :
    (litStep π r l).cnt ≤ r.cnt + 1 := by
  unfold litStep
  split_ifs <;> simp

/-- **What the literal loop computes**: the number of literals not falsified, whether one of them
holds, the code of the last of them, and the first open variable. -/
theorem foldl_litStep (π : List (Literal ℕ)) (ls : Clause ℕ) (r : LitRegs) :
    (ls.foldl (litStep π) r).cnt = r.cnt + (notFalse π ls).length ∧
      (ls.foldl (litStep π) r).sat = (r.sat || ls.any (Holds π)) ∧
      (ls.foldl (litStep π) r).uc = ((notFalse π ls).getLast?.map litCode).getD r.uc ∧
      (ls.foldl (litStep π) r).opened =
        r.opened.or ((ls.map Prod.fst).find? fun x => !Assigned π x) := by
  induction ls generalizing r with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih (litStep π r l)
    rw [List.foldl_cons, h₁, h₂, h₃, h₄]
    have hopen := not_assigned_iff π l
    have hlast : ((l :: notFalse π ls).getLast?.map litCode).getD r.uc =
        ((notFalse π ls).getLast?.map litCode).getD (litCode l) := by
      rw [List.getLast?_cons]; cases (notFalse π ls).getLast? <;> rfl
    unfold litStep
    cases hn : π.contains l.negate <;> cases hp : π.contains l <;>
      simp only [hn, hp, Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false]
        at hopen <;>
      simp only [notFalse, List.filter_cons, hn, hp, Holds, ← hopen, Bool.false_eq_true,
        ↓reduceIte, List.length_cons, List.any_cons, List.map_cons, List.find?_cons,
        Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_or,
        Bool.or_true, Bool.true_or, Option.or_assoc, Option.some_or, and_true] <;>
      first | done | exact ⟨by omega, trivial, hlast.symm⟩

theorem notFalse_eq_nil_iff (π : List (Literal ℕ)) (c : Clause ℕ) :
    notFalse π c = [] ↔ Falsifies π c = true := by
  simp [notFalse, List.filter_eq_nil_iff, Falsifies]

/-- The code of the literal of a unit clause. -/
def unitCode (π : List (Literal ℕ)) (c : Clause ℕ) : Option ℕ :=
  match Clause.unit? (notFalse π c) with
  | some l => if π.contains l then none else some (litCode l)
  | none => none

theorem codeOn_litCode (π : List (Literal ℕ)) (l : Literal ℕ) :
    codeOn π (litCode l) = π.contains l := by
  unfold codeOn
  rw [Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨_, hl', h⟩ => litCodeBy_injective Function.injective_id (by simpa using h) ▸ hl',
    fun h => ⟨l, h, by simp⟩⟩

theorem unitCode_eq (π : List (Literal ℕ)) (c : Clause ℕ) (o : Option ℕ) :
    (if (c.foldl (litStep π) ⟨0, 0, false, o⟩).cnt == 1 &&
        !codeOn π (c.foldl (litStep π) ⟨0, 0, false, o⟩).uc
      then some (c.foldl (litStep π) ⟨0, 0, false, o⟩).uc else none) = unitCode π c := by
  obtain ⟨h₁, -, h₃, -⟩ := foldl_litStep π c ⟨0, 0, false, o⟩
  simp only at h₁ h₃
  simp only [h₁, h₃, unitCode, Nat.zero_add]
  rcases hf : notFalse π c with _ | ⟨l, _ | ⟨l', f⟩⟩
  · simp
  · simp [Clause.unit?, codeOn_litCode]
  · simp [Clause.unit?]

theorem unitLiteral?_map (φ : CNF ℕ) (π : List (Literal ℕ)) :
    (unitLiteral? φ π).map litCode = φ.findSome? (unitCode π) := by
  rw [unitLiteral?, List.map_findSome?]
  congr 1
  funext c
  simp only [Function.comp_apply]
  cases h : Clause.unit? (notFalse π c) with
  | none => simp [unitCode, h]
  | some l => by_cases hl : l ∈ π <;> simp [unitCode, h, hl]

/-- **What the scan computes**, from any registers. -/
theorem foldl_clauseStep (π : List (Literal ℕ)) (φ : CNF ℕ) (s : ScanRegs) :
    φ.foldl (clauseStep π) s =
      ⟨s.conf || φ.any (Falsifies π), s.alls && φ.all (fun c => c.any (Holds π)),
        s.unit.or (φ.findSome? (unitCode π)),
        s.opened.or (φ.vars.find? fun x => !Assigned π x)⟩ := by
  induction φ generalizing s with
  | nil => cases s; simp [CNF.vars]
  | cons c φ ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨h₁, h₂, -, h₄⟩ := foldl_litStep π c ⟨0, 0, false, s.opened⟩
    have hu := unitCode_eq π c s.opened
    have hF : Falsifies π c = ((notFalse π c).length == 0) := by
      rw [Bool.eq_iff_iff, ← notFalse_eq_nil_iff]; simp
    simp only [Nat.zero_add, Bool.false_or] at h₁ h₂ h₄
    simp only [clauseStep, endClause, hu]
    simp only [h₁, h₂, h₄, hF, List.any_cons, List.all_cons, List.findSome?_cons, CNF.vars,
      List.flatten_cons, List.map_append, List.find?_append, Bool.or_assoc, Bool.and_assoc,
      Option.or_assoc]
    refine ScanRegs.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
    cases s.unit <;> cases unitCode π c <;> rfl

/-- **The scan computes the status of the trail**: whether a clause is falsified, whether every
clause has a true literal, the code of the literal of the first unit clause, and the variable of
the first literal occurrence that is open. -/
theorem foldl_clauseStep_init (π : List (Literal ℕ)) (φ : CNF ℕ) :
    φ.foldl (clauseStep π) .init =
      ⟨φ.any (Falsifies π), φ.all (fun c => c.any (Holds π)), (unitLiteral? φ π).map litCode,
        φ.vars.find? fun x => !Assigned π x⟩ := by
  rw [foldl_clauseStep, unitLiteral?_map]
  simp [ScanRegs.init]

/-- The code left by the literal loop is `0` or that of a literal not falsified. -/
theorem uc_foldl_litStep (π : List (Literal ℕ)) (c : Clause ℕ) (o : Option ℕ) :
    (c.foldl (litStep π) ⟨0, 0, false, o⟩).uc = 0 ∨
      ∃ l ∈ notFalse π c, (c.foldl (litStep π) ⟨0, 0, false, o⟩).uc = litCode l := by
  obtain ⟨-, -, h, -⟩ := foldl_litStep π c ⟨0, 0, false, o⟩
  rw [h]
  cases hl : (notFalse π c).getLast? with
  | none => simp
  | some l => exact .inr ⟨l, List.mem_of_getLast? hl, by simp⟩

/-! ### The program computes the fold -/

/-- The literal array at `T` holds the partial assignment `π` on the variables below `N`: the cell
`T + 2 v + b` is `1` when `(v, b)` is in `π` and `0` otherwise. -/
def LitArr (mem : ℕ → ℕ) (T N : ℕ) (π : List (Literal ℕ)) : Prop :=
  ∀ l : Literal ℕ, l.1 < N → mem (T + litCode l) = (π.contains l).toNat

theorem litCode_lt {l : Literal ℕ} {N : ℕ} (h : l.1 < N) : litCode l < 2 * N := by
  obtain ⟨v, b⟩ := l
  simp only at h
  cases b <;> simp [litCodeBy] <;> omega

open Cslib.WordRAM Cslib.WordRAM.Block Reg

/-- The registers of the literal loop hold `r`. -/
def LitAt (y : Data 32) (r : LitRegs) : Prop :=
  y.regs cnt = r.cnt ∧ y.regs uc = r.uc ∧ y.regs sat = r.sat.toNat ∧
    y.regs opf = r.opened.isSome.toNat ∧ y.regs ov = r.opened.getD 0

/-- The scan registers hold `s`. -/
def ScanAt (y : Data 32) (s : ScanRegs) : Prop :=
  y.regs conf = s.conf.toNat ∧ y.regs alls = s.alls.toNat ∧ y.regs uf = s.unit.isSome.toNat ∧
    y.regs unit = s.unit.getD 0 ∧ y.regs opf = s.opened.isSome.toNat ∧
    y.regs ov = s.opened.getD 0

section Specs

variable {w : ℕ}

attribute [local wram_simps] LitAt ScanAt Bool.toNat_false Bool.toNat_true Option.isSome_none
  Option.isSome_some Option.getD_none Option.getD_some

/-- One literal of the scan performs `litStep`. -/
theorem litBody_spec (π : List (Literal ℕ)) (l : Literal ℕ) (r : LitRegs) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hlit : x.mem (x.regs lptr) = litCode l) (hlN : l.1 < N)
    (hπ : LitArr x.mem (x.regs tb) N π) (hr : LitAt x r)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitp : Fits w (x.regs lptr + 1))
    (hfitc : Fits w (r.cnt + 1)) :
    ∃ y, ExecWithin w litBody x y 15 ∧ y.mem = x.mem ∧ LitAt y (litStep π r l) ∧
      y.regs lptr = x.regs lptr + 1 := by
  obtain ⟨c, u, s, o⟩ := r
  obtain ⟨hcnt, huc, hsat, hopf, hov⟩ := hr
  have hc := litCode_lt hlN
  have hnc := litCode_lt (l := l.negate) hlN
  have hvl := hπ l hlN
  have hvn := hπ l.negate hlN
  have hxor : litCode l ^^^ 1 = litCode l.negate := litCodeBy_xor_one _root_.id l
  have hshr : litCode l >>> 1 = l.1 := litCodeBy_shiftRight _root_.id l
  refine WP.exists_execWithin ?_
  unfold litBody
  cases hn : π.contains l.negate <;> cases hp : π.contains l <;> cases o <;>
    simp only [hn, hp, Bool.toNat_false, Bool.toNat_true, Option.isSome_none, Option.isSome_some,
      Option.getD_none, Option.getD_some] at hvl hvn hopf hov <;>
    wram_exec [hlit, hone, hzero, hvl, hvn, hxor, hshr, hcnt, huc, hsat, hopf, hov] <;>
    wram_simp [litStep, hn, hp, hsat, huc, hopf, hov] <;> simp

/-- **The literal loop** folds `litStep` over the literals at `lptr`, and leaves memory
unchanged. -/
theorem litLoop_spec (π : List (Literal ℕ)) (ls : Clause ℕ) (r : LitRegs) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hend : x.regs lend = x.regs lptr + ls.length) (hN : ∀ l ∈ ls, l.1 < N)
    (hπ : LitArr x.mem (x.regs tb) N π) (hr : LitAt x r)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitp : Fits w (x.regs lend + 1))
    (hfitc : Fits w (r.cnt + ls.length + 1)) :
    ∃ y, ExecWithin w litLoop x y (17 * ls.length + 2) ∧ y.mem = x.mem ∧
      LitAt y (ls.foldl (litStep π) r) ∧ y.regs lptr = x.regs lend := by
  wram_fold (fun rest y => ∃ r', y.mem = x.mem ∧ y.regs lptr + rest.length = x.regs lend ∧
      (∀ l ∈ rest, l.1 < N) ∧ HoldsList (y.regs lptr) (rest.map litCode) x.mem ∧ LitAt y r' ∧
      Fits w (r'.cnt + rest.length + 1) ∧ rest.foldl (litStep π) r' = ls.foldl (litStep π) r)
    over ls cost (fun _ => 15)
  case init => exact ⟨r, rfl, hend.symm, hN, hl, hr, hfitc, rfl⟩
  case exit => rintro v m ⟨-, -, he, -⟩; omega
  case step =>
    rintro l rest v m ⟨r', rfl, he, hN', hl', hr', hfc, hsc⟩
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp (by simpa using hl')
    have hlN := hN' l (by simp)
    have := litStep_cnt_le π r' l
    refine ⟨by omega, ?_⟩
    wram_call (litBody_spec π l r' _ N ..) framed with v' m' ⟨rfl, hz, hzp⟩
    exact ⟨_, rfl, by omega, fun l' h => hN' l' (by simp [h]), hzp ▸ hrest, hz,
      hfc.of_le (by omega), hsc⟩
  case post =>
    rintro v m ⟨r', rfl, he, -, -, hr', -, hsc⟩
    exact ⟨by simp; omega, rfl, hsc ▸ hr', he⟩

/-- The end of a clause performs `endClause`. -/
theorem clauseEnd_spec (π : List (Literal ℕ)) (r : LitRegs) (s : ScanRegs) (x : Data 32)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (hr : LitAt x r)
    (hconf : x.regs conf = s.conf.toNat) (halls : x.regs alls = s.alls.toNat)
    (huf : x.regs uf = s.unit.isSome.toNat) (hunit : x.regs unit = s.unit.getD 0)
    (hu : r.cnt = 1 → x.mem (x.regs tb + r.uc) = (codeOn π r.uc).toNat)
    (hfit : Fits w (x.regs tb + r.uc)) :
    ∃ y, ExecWithin w clauseEnd x y 13 ∧ y.mem = x.mem ∧ ScanAt y (endClause π s r) ∧
      y.regs ptr = x.regs lend := by
  obtain ⟨k, u, b, o⟩ := r
  obtain ⟨sc, sa, su, so⟩ := s
  obtain ⟨hcnt, huc, hsat, hopf, hov⟩ := hr
  simp only at hcnt huc hsat hopf hov hconf halls huf hunit hu hfit
  refine WP.exists_execWithin ?_
  unfold clauseEnd
  rcases Nat.lt_trichotomy k 1 with hk | rfl | hk
  · obtain rfl : k = 0 := by omega
    cases b <;>
      wram_exec [hcnt, hsat, hzero, hone] <;>
      wram_simp [endClause, hconf, halls, huf, hunit, hopf, hov] <;> simp
  · have hmem := hu rfl
    cases su <;> cases b <;> cases hco : codeOn π u <;> rw [hco] at hmem <;>
      wram_exec [hcnt, huc, hsat, huf, hzero, hone, hmem] <;>
      wram_simp [endClause, hco, hconf, halls, huf, hunit, hopf, hov] <;> simp
  · have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    cases b <;>
      wram_exec [hcnt, hsat, hzero, hone, hk0, hk1] <;>
      wram_simp [endClause, hconf, halls, huf, hunit, hopf, hov,
        beq_false_of_ne hk0, beq_false_of_ne hk1] <;> simp

private theorem sum_scan_cost (ψ : CNF ℕ) :
    (ψ.map fun c => 17 * c.length + 21 + 2).sum ≤ 23 * (ψ.flatMap encodeClause).length := by
  induction ψ with
  | nil => simp
  | cons c ψ ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      length_encodeClauseBy]
    omega

/-- **The clause loop** folds `clauseStep` over the clauses from `ptr` to `cend`, and leaves
memory unchanged. -/
theorem clauseLoop_spec (π : List (Literal ℕ)) (ψ : CNF ℕ) (s : ScanRegs) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcl : HoldsList (x.regs ptr) (ψ.flatMap encodeClause) x.mem)
    (hend : x.regs ptr + (ψ.flatMap encodeClause).length = x.regs cend)
    (hN : ∀ c ∈ ψ, ∀ l ∈ c, l.1 < N) (hπ : LitArr x.mem (x.regs tb) N π) (hs : ScanAt x s)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitp : Fits w (x.regs cend + 1)) :
    ∃ y, ExecWithin w clauseLoop x y (23 * (ψ.flatMap encodeClause).length + 2) ∧
      y.mem = x.mem ∧ ScanAt y (ψ.foldl (clauseStep π) s) := by
  wram_fold (fun rest y => ∃ s', y.mem = x.mem ∧
      y.regs ptr + (rest.flatMap encodeClause).length = x.regs cend ∧
      (∀ c ∈ rest, ∀ l ∈ c, l.1 < N) ∧
      HoldsList (y.regs ptr) (rest.flatMap encodeClause) x.mem ∧ ScanAt y s' ∧
      rest.foldl (clauseStep π) s' = ψ.foldl (clauseStep π) s)
    over ψ cost (fun c => 17 * c.length + 21)
  case init => exact ⟨s, rfl, hend, hN, hcl, hs, rfl⟩
  case exit => rintro v m ⟨-, -, he, -⟩; simp at he; omega
  case step =>
    rintro c rest v m ⟨s', rfl, he, hN', hcl', ⟨hconf, halls, huf, hunit, hopf, hov⟩, hsc⟩
    simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy] at he hcl'
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hcl'
    obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp hpc
    simp only [length_encodeClauseBy] at hpψ
    have hNc := hN' c (by simp)
    refine ⟨by omega, ?_⟩
    wram_exec [clauseBody, hlen, hone, hzero]
    wram_call (litLoop_spec (w := w) π c ⟨0, 0, false, s'.opened⟩ _ N ..) framed
      with v₂ m₂ ⟨rfl, hr₂, hp₂⟩
    set r := c.foldl (litStep π) ⟨0, 0, false, s'.opened⟩ with hr
    have hu : r.cnt = 1 → x.mem (x.regs tb + r.uc) = (codeOn π r.uc).toNat := fun h1 => by
      obtain ⟨hcnt, -, huc, -⟩ := foldl_litStep π c ⟨0, 0, false, s'.opened⟩
      rw [← hr] at hcnt huc
      cases hl : (notFalse π c).getLast? with
      | none => rw [List.getLast?_eq_none_iff.1 hl] at hcnt; simp [h1] at hcnt
      | some l =>
        rw [huc, hl, Option.map_some, Option.getD_some, codeOn_litCode]
        exact hπ l (hNc l (List.mem_of_mem_filter (List.mem_of_getLast? hl)))
    have hucN : r.uc ≤ 2 * N := by
      rcases uc_foldl_litStep π c s'.opened with h | ⟨l, hl, h⟩
      · rw [hr, h]; omega
      · rw [hr, h]; exact (litCode_lt (hNc l (List.mem_of_mem_filter hl))).le
    wram_call (clauseEnd_spec (w := w) π r s' _ ..) framed with v₃ m₃ ⟨rfl, hs₃, hp₃⟩
    exact ⟨by omega, _, rfl, by omega, fun c' h => hN' c' (by simp [h]),
      hp₃ ▸ (show v ptr + 1 + c.length = v ptr + (c.length + 1) by omega) ▸ hpψ, hs₃, hsc⟩
  case post =>
    rintro v m ⟨s', rfl, he, -, -, hs', hsc⟩
    exact ⟨by have := sum_scan_cost ψ; omega, rfl, hsc ▸ hs'⟩

/-- **The scan** of the clauses `φ` stored from address `2` to `cend` against the partial
assignment `π`: the registers end with the status of `π`, and memory is unchanged. -/
theorem scan_spec (π : List (Literal ℕ)) (φ : CNF ℕ) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hcl : HoldsList 2 (φ.flatMap encodeClause) x.mem)
    (hend : 2 + (φ.flatMap encodeClause).length = x.regs cend)
    (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) (hπ : LitArr x.mem (x.regs tb) N π)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitp : Fits w (x.regs cend + 1)) :
    ∃ y, ExecWithin w scan x y (23 * (φ.flatMap encodeClause).length + 9) ∧ y.mem = x.mem ∧
      ScanAt y ⟨φ.any (Falsifies π), φ.all (fun c => c.any (Holds π)),
        (unitLiteral? φ π).map litCode, φ.vars.find? fun x => !Assigned π x⟩ := by
  refine WP.exists_execWithin ?_
  wram_exec [scan, hzero, hone, htwo]
  wram_call (clauseLoop_spec (w := w) π φ .init _ N ..) framed [ScanRegs.init]
    with v m ⟨rfl, hs⟩
  rw [show (⟨false, true, none, none⟩ : ScanRegs) = .init from rfl, foldl_clauseStep_init] at hs
  exact ⟨by omega, rfl, hs⟩

end Specs

end Cslib.Algorithms.WordRAM.DPLL

end
