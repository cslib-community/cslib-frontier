/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.MemoryView

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.PPSZ.Clauses
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.Nat.Bitwise

/-!
# w-implication on the word RAM

`Cslib.Algorithms.WordRAM.PPSZ.impliedCode` computes the value w-implied on a variable
(`Cslib.Complexity.PPSZ.implied`), the oracle of PPSZ. The formula is stored as in
`Cslib.Algorithms.WordRAM.Schoening.encodeClauses`, the partial assignment as in
`Cslib.Algorithms.WordRAM.PPZ.PartialAt`, and the bound `s` on the number of clauses is stored in
the word after a scratch base address. The program runs the search
`Cslib.Algorithms.WordRAM.PPSZ.addrTest` for the polarity `true`, then, if needed, for `false`:

* an odometer `D` steps through every choice of `s` clause addresses
  (`Cslib.Algorithms.WordRAM.PPSZ.outerSearch`), and for each, an odometer `E` steps through every
  choice of one literal address in each chosen clause
  (`Cslib.Algorithms.WordRAM.PPSZ.innerSearch`);
* a choice of literals is tested for compatibility (`Cslib.Algorithms.WordRAM.PPSZ.goodTest`): no
  chosen literal is falsified by the partial assignment with `x` set to `!b`, and no two are
  complementary;
* `x = b` is implied when the assignment already sets `x` to `b`, or some choice of clauses has no
  compatible choice of literals.

Both odometers step with `Cslib.Algorithms.WordRAM.PPSZ.nextSection`, so they visit every section
(`Cslib.Algorithms.WordRAM.PPSZ.nextSection_sections`). The arrays `D` and `E` take `2 s` words of
scratch memory, which the program sets back to zero at the end. On scratch memory that starts out
zero, `Cslib.Algorithms.WordRAM.PPSZ.impliedCode_spec` therefore leaves memory unchanged and
stores the word of `implied φ s τ x`.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.ImpFrame`: the registers and memory the search relies on.
* `Cslib.Algorithms.WordRAM.PPSZ.initD`, `Cslib.Algorithms.WordRAM.PPSZ.incD`,
  `Cslib.Algorithms.WordRAM.PPSZ.initE`, `Cslib.Algorithms.WordRAM.PPSZ.incE`: the odometers.
* `Cslib.Algorithms.WordRAM.PPSZ.goodTest`: the compatibility test.
* `Cslib.Algorithms.WordRAM.PPSZ.innerSearch`, `Cslib.Algorithms.WordRAM.PPSZ.outerSearch`,
  `Cslib.Algorithms.WordRAM.PPSZ.impScan`: the nested search.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedCode`: the implied value.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedTime`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.impScan_spec`: the search decides w-implication.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedCode_spec`: the implied value, within
  `impliedTime s E` instructions, where `E` is the length of the encoding of the clauses.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedTime_le`: `impliedTime s E ≤ 140 (s + 1)² (E + 1)^(2 s)`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPSZ
open Cslib.Algorithms.WordRAM.Schoening (litCode encodeClause encodeClauses litCode_lt
  litCode_shiftRight litCode_and_one encodeClauses_cons length_encodeClause)
open Cslib.Algorithms.WordRAM.PPZ (optCode PartialAt)
open Cslib.Algorithms.WordRAM.PPZ.Reg

variable {n : ℕ}

/-! ### Registers -/

namespace Reg

/-- The bound `s` on the number of clauses. -/
abbrev sReg : Fin 32 := 6
/-- Address of the array `D` of chosen clause addresses. -/
abbrev dBase : Fin 32 := 7
/-- Address of the array `E` of chosen literal addresses, `dBase + s`. -/
abbrev eBase : Fin 32 := 8
/-- Index into `D` and `E`. -/
abbrev jR : Fin 32 := 9
/-- Second index into `E`. -/
abbrev kR : Fin 32 := 10
/-- Scratch address. -/
abbrev adr : Fin 32 := 11
/-- A clause address. -/
abbrev dv : Fin 32 := 12
/-- A literal address. -/
abbrev ev : Fin 32 := 13
/-- A clause length, or a word of the partial assignment. -/
abbrev lenR : Fin 32 := 14
/-- An end address, or a comparison value. -/
abbrev stop : Fin 32 := 15
/-- A literal code. -/
abbrev litR : Fin 32 := 16
/-- A variable, or the code of the complementary literal. -/
abbrev auxR : Fin 32 := 17
/-- The result of a test or search. -/
abbrev sat : Fin 32 := 18
/-- Whether the clause odometer continues. -/
abbrev contO : Fin 32 := 26
/-- Whether the literal odometer continues. -/
abbrev contI : Fin 32 := 27
/-- A sign. -/
abbrev sgnR : Fin 32 := 28

end Reg

open Reg

/-! ### The frame of the search -/

/-- The registers and memory the search relies on: the constants, the variable `x`, the polarity
`b`, the clauses of `φ` stored from `C`, the partial assignment `τ` stored from `Tb`, the bound `s`,
and the arrays `D` at `Db` and `E` at `Db + s`, above the clauses, the partial assignment and the
literal codes. -/
structure ImpFrame (w : ℕ) (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (b : Bool)
    (C Tb s Db : ℕ) (y : Data 32) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  x_eq : y.regs xReg = x
  b_eq : y.regs bReg = b.toNat
  cBeg_eq : y.regs cBeg = C
  cEnd_eq : y.regs cEnd = C + (encodeClauses φ).length
  tBase_eq : y.regs tBase = Tb
  s_eq : y.regs sReg = s
  dBase_eq : y.regs dBase = Db
  eBase_eq : y.regs eBase = Db + s
  clauses : HoldsList C (encodeClauses φ) y.mem
  stored : PartialAt y.mem Tb τ
  clauses_le : C + (encodeClauses φ).length ≤ Db
  stored_le : Tb + n ≤ Db
  codes_le : 2 * n ≤ Db
  fits : Fits w (Db + 2 * s + 1)

/-- Code that writes none of the registers of `ImpFrame`. -/
def PreservesImp (c : Code .standard 32) : Prop :=
  c.Preserves zero ∧ c.Preserves one ∧ c.Preserves xReg ∧ c.Preserves bReg ∧ c.Preserves cBeg ∧
    c.Preserves cEnd ∧ c.Preserves tBase ∧ c.Preserves sReg ∧ c.Preserves dBase ∧
    c.Preserves eBase

instance (c : Code .standard 32) : Decidable (PreservesImp c) :=
  inferInstanceAs (Decidable (_ ∧ _))

section Frame

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The frame survives a change that keeps its registers and the memory below `Db`. -/
theorem ImpFrame.congr {y z : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y)
    (hr : ∀ i ∈ ({zero, one, xReg, bReg, cBeg, cEnd, tBase, sReg, dBase, eBase} :
      Finset (Fin 32)), z.regs i = y.regs i)
    (hm : ∀ a < Db, z.mem a = y.mem a) : ImpFrame w φ τ x b C Tb s Db z where
  zero_eq := (hr zero (by decide)).trans h.zero_eq
  one_eq := (hr one (by decide)).trans h.one_eq
  x_eq := (hr xReg (by decide)).trans h.x_eq
  b_eq := (hr bReg (by decide)).trans h.b_eq
  cBeg_eq := (hr cBeg (by decide)).trans h.cBeg_eq
  cEnd_eq := (hr cEnd (by decide)).trans h.cEnd_eq
  tBase_eq := (hr tBase (by decide)).trans h.tBase_eq
  s_eq := (hr sReg (by decide)).trans h.s_eq
  dBase_eq := (hr dBase (by decide)).trans h.dBase_eq
  eBase_eq := (hr eBase (by decide)).trans h.eBase_eq
  clauses := by
    have hs := h.clauses_le
    ram_keep h.clauses using hm
  stored := fun v => (hm _ (by have := h.stored_le; omega)).trans (h.stored v)
  clauses_le := h.clauses_le
  stored_le := h.stored_le
  codes_le := h.codes_le
  fits := h.fits

/-- A run of code that keeps the frame registers and the memory below `Db` keeps the frame. -/
theorem ImpFrame.of_exec {c : Code .standard 32} {y z : Data 32} {T : ℕ}
    (h : ImpFrame w φ τ x b C Tb s Db y) (hc : PreservesImp c) (he : ExecWithin w c y z T)
    (hm : ∀ a < Db, z.mem a = y.mem a) : ImpFrame w φ τ x b C Tb s Db z := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc
  refine h.congr (fun i hi => ?_) hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact he.regs_eq ‹_›

/-- The frame after setting a register outside it. -/
theorem ImpFrame.set {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) {i : Fin 32}
    (hi : i ∉ ({zero, one, xReg, bReg, cBeg, cEnd, tBase, sReg, dBase, eBase} :
      Finset (Fin 32))) (v : ℕ) : ImpFrame w φ τ x b C Tb s Db (y.set i v) :=
  h.congr (fun j hj => by
    rw [Data.set_regs, Function.update_of_ne]
    rintro rfl
    exact hi hj) fun _ _ => rfl

/-- The frame after a store at or above `Db`. -/
theorem ImpFrame.write {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) {a : ℕ} (ha : Db ≤ a)
    (v : ℕ) : ImpFrame w φ τ x b C Tb s Db (y.write a v) :=
  h.congr (fun _ _ => rfl) fun a' ha' => by
    rw [Data.write_mem, Function.update_of_ne (by omega)]

/-- Values up to the end of the arrays fit a word. -/
private theorem ImpFrame.fits_le {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) {v : ℕ}
    (hv : v ≤ Db + 2 * s + 1) : Fits w v :=
  h.fits.of_le hv

/-- Shared wrapper for stepping an odometer carry loop from index `0` and setting `cont` to
`jR - sReg`: `1` when `nextSection` produces a successor (`jR = s + 1`) and `0` at exhaustion
(`jR = s`). -/
private theorem odometer_step_spec {base hi k : ℕ} {loop : Code .standard 32} {cont : Fin 32}
    (hcont : cont ∉ ({zero, one, xReg, bReg, cBeg, cEnd, tBase, sReg, dBase, eBase} :
      Finset (Fin 32)))
    {L : List (List ℕ)} {u : List ℕ} {y : Data 32}
    (hf : ImpFrame w φ τ x b C Tb s Db y)
    (hloop : ∃ z, ExecWithin w loop (y.set jR 0) z (k * s + 2) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < base ∨ hi ≤ a → z.mem a = (y.set jR 0).mem a) ∧
      (∀ u', nextSection L u = some u' → z.regs jR = s + 1 ∧ HoldsList base u' z.mem) ∧
      (nextSection L u = none → z.regs jR = s)) :
    ∃ z, ExecWithin w ram[ jR ← zero; ⟪loop⟫; cont ← jR - sReg ] y z (k * s + 4) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < base ∨ hi ≤ a → z.mem a = y.mem a) ∧
      (∀ u', nextSection L u = some u' → z.regs cont = 1 ∧ HoldsList base u' z.mem) ∧
      (nextSection L u = none → z.regs cont = 0) := by
  wram_exec [hf.zero_eq]
  wram_call hloop with z ⟨hzf, hzm, hzs, hzn⟩
  have hjz : z.regs jR ≤ s + 1 := by
    rcases hns : nextSection L u with _ | u'
    · rw [hzn hns]; omega
    · rw [(hzs u' hns).1]
  wram_exec [hzf.fits_le, hzf.s_eq]
  exact ⟨hzf.set hcont _, fun a ha => hzm a ha,
    fun u' h => ⟨by wram_simp [(hzs u' h).1], (hzs u' h).2⟩,
    fun h => by wram_simp [hzn h]⟩

end Frame

local macro "imp_frame " hf:term : tactic => `(tactic| (
  refine ImpFrame.congr $hf (fun i hi => ?_) (fun a ha => by try wram_simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h <;> (subst h; try wram_simp)))

/-! ### The clause odometer -/

/-- Set `D[j]` to the first clause address. -/
def initDBody : Code .standard 32 := ram[ adr ← dBase + jR; *adr ← cBeg; jR ← jR + one ]

/-- Set `D[j], …, D[s - 1]` to the first clause address. -/
def initDLoop : Code .standard 32 := .loop (.lt jR sReg) initDBody

/-- **Start the clause odometer**: every entry of `D` is the first clause address. -/
def initD : Code .standard 32 := ram[ jR ← zero; ⟪initDLoop⟫ ]

/-- Advance `D[j]` to the next clause address, or, after the last clause, return it to the first
one and carry into `D[j + 1]`. Without a carry, `jR` becomes `s + 1` and the loop stops. -/
def incDBody : Code .standard 32 := ram[
  adr ← dBase + jR; dv ← *adr; lenR ← *dv; dv ← dv + one; dv ← dv + lenR;
  if dv = cEnd then [ *adr ← cBeg; jR ← jR + one ] else [ *adr ← dv; jR ← sReg + one ] ]

/-- The carries of the clause odometer from `D[j]` on. -/
def incDLoop : Code .standard 32 := .loop (.lt jR sReg) incDBody

/-- **Step the clause odometer**: `contO` becomes `0` after the last choice of clauses, and `1`
otherwise. -/
def incD : Code .standard 32 := ram[ jR ← zero; ⟪incDLoop⟫; contO ← jR - sReg ]

section ClauseOdometer

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- Shared specification for filling `d` consecutive words starting at `dBase + jR` with the
register value `valR` up to limit register `limR`, used by both `initDLoop_spec` and
`zeroLoop_spec`. -/
private theorem fillDLoop_spec {limR valR : Fin 32} (hlim_ne : limR ≠ jR ∧ limR ≠ adr)
    (hval_ne : valR ≠ jR ∧ valR ≠ adr) {lim val : ℕ}
    (hle_lim : lim ≤ 2 * s) (hfit_val : Fits w val) :
    ∀ (d : ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
      y.regs limR = lim → y.regs valR = val → y.regs jR + d = lim →
      ∃ z, ExecWithin w
          (.loop (.lt jR limR) ram[ adr ← dBase + jR; *adr ← valR; jR ← jR + one ])
          y z (5 * d + 2) ∧
        ImpFrame w φ τ x b C Tb s Db z ∧
        HoldsList (Db + y.regs jR) (List.replicate d val) z.mem ∧
        ∀ a, a < Db + y.regs jR ∨ Db + lim ≤ a → z.mem a = y.mem a
  | 0, y, hf, hlim, _, hd => by
    have hc : ¬(Cond.lt jR limR).Holds y := by simp [Cond.holds_lt, hlim]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, by simp [holdsList_nil],
      fun _ _ => rfl⟩
  | d + 1, y, hf, hlim, hval, hd => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd ⊢
    have hc : (Cond.lt jR limR).Holds y := by simp [Cond.holds_lt, hlim, hj]; omega
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    wram_exec [hf.fits_le, hf.dBase_eq, hf.one_eq, hj, hval, hfit_val]
    wram_call (fillDLoop_spec hlim_ne hval_ne hle_lim hfit_val d _ (by imp_frame hf)
      (by wram_simp [hlim_ne.1, hlim_ne.2, hlim])
      (by wram_simp [hval_ne.1, hval_ne.2, hval])
      (by wram_simp; omega))
      with z ⟨hzf, hzl, hzm⟩
    wram_simp at hzl hzm
    refine ⟨by omega, hzf, ?_, fun a ha => (hzm a (by omega)).trans (by wram_simp)⟩
    rw [List.replicate_succ, holdsList_cons_iff]
    exact ⟨(hzm _ (by omega)).trans (by wram_simp), by simpa [Nat.add_assoc] using hzl⟩

/-- Unpacks a non-empty suffix `a :: u` of clause addresses stored at `Db + j`: the loop condition
`jR < sReg` holds, `a` is a valid clause address in `[C, C + (encodeClauses φ).length]`, `D[j] = a`,
and `y.mem a` holds the length of `clauseOf C φ a`. -/
private theorem clauseCons_step {a : ℕ} {u : List ℕ} {y : Data 32}
    (hf : ImpFrame w φ τ x b C Tb s Db y) (j : ℕ) (hj : y.regs jR = j)
    (hd : j + (a :: u).length = s) (hA : ∀ a' ∈ a :: u, a' ∈ clauseAddrs C φ)
    (hl : HoldsList (Db + j) (a :: u) y.mem) :
    (Cond.lt jR sReg).Holds y ∧ a ∈ clauseAddrs C φ ∧
      a + 1 + (clauseOf C φ a).length ≤ C + (encodeClauses φ).length ∧
      y.mem (Db + j) = a ∧ HoldsList (Db + j + 1) u y.mem ∧
      y.mem a = (clauseOf C φ a).length := by
  have haA : a ∈ clauseAddrs C φ := hA a (by simp)
  obtain ⟨hla, hlu⟩ := holdsList_cons_iff.mp hl
  exact ⟨by simp [Cond.holds_lt, hf.s_eq, hj]; simp at hd; omega,
    haA, (bounds_of_mem_clauseAddrs haA).2, hla, hlu, mem_clauseAddr hf.clauses haA⟩

/-- **The start loop of the clause odometer** from entry `j`: it stores the first clause address
in `D[j], …, D[s - 1]` and keeps the memory outside them. -/
private theorem initDLoop_spec : ∀ (d : ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs jR + d = s →
    ∃ z, ExecWithin w initDLoop y z (5 * d + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      HoldsList (Db + y.regs jR) (List.replicate d C) z.mem ∧
      ∀ a, a < Db + y.regs jR ∨ Db + s ≤ a → z.mem a = y.mem a :=
  fun d y hf hd =>
    fillDLoop_spec ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by omega)
      (hf.fits_le (by have := hf.clauses_le; omega)) d y hf hf.s_eq hf.cBeg_eq hd

/-- **Start the clause odometer**: `D` holds `s` copies of the first clause address, and the
memory outside `D` is unchanged, within `5 s + 3` instructions. -/
theorem initD_spec (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w initD y z (5 * s + 3) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      HoldsList Db (List.replicate s C) z.mem ∧
      ∀ a, a < Db ∨ Db + s ≤ a → z.mem a = y.mem a := by
  unfold initD
  wram_exec [hf.zero_eq]
  wram_call (initDLoop_spec s _ (by imp_frame hf) (by wram_simp))
    with z ⟨hzf, hzl, hzm⟩
  wram_simp at hzl hzm
  exact ⟨by omega, hzf, hzl, hzm⟩

/-- **The carry loop of the clause odometer** from entry `j`, on a choice `u` of clause addresses
in `D[j], …`: if the odometer step on `u` has a result, `D[j], …` holds it and `jR = s + 1`; if
not, `jR = s`. The memory outside `D[j], …, D[s - 1]` is unchanged. -/
private theorem incDLoop_spec : ∀ (u : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs jR + u.length = s → (∀ a ∈ u, a ∈ clauseAddrs C φ) →
    HoldsList (Db + y.regs jR) u y.mem →
    ∃ z, ExecWithin w incDLoop y z (12 * u.length + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + y.regs jR ∨ Db + s ≤ a → z.mem a = y.mem a) ∧
      (∀ u', nextSection (List.replicate u.length (clauseAddrs C φ)) u = some u' →
        z.regs jR = s + 1 ∧ HoldsList (Db + y.regs jR) u' z.mem) ∧
      (nextSection (List.replicate u.length (clauseAddrs C φ)) u = none → z.regs jR = s)
  | [], y, hf, hd, _, _ => by
    simp only [List.length_nil, Nat.add_zero] at hd
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    refine ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun _ _ => rfl, ?_, ?_⟩
    · intro u' h; simp [nextSection] at h
    · intro _; simpa using hd
  | a :: u, y, hf, hd, hA, hl => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd hl ⊢
    obtain ⟨hc, haA, hb_hi, hla, hlu, hlen⟩ := clauseCons_step hf j hj hd hA hl
    simp only [List.length_cons] at hd
    have hcl_le := hf.clauses_le
    set len := (clauseOf C φ a).length with hlen_def
    have hsucc : succIn (clauseAddrs C φ) a =
        if a + 1 + len = C + (encodeClauses φ).length then none else some (a + 1 + len) :=
      succIn_clauseAddrs haA
    have hhead : (clauseAddrs C φ).headD 0 = C :=
      headD_clauseAddrs (fun h => by simp [h, clauseAddrs] at haA) 0
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold incDBody
    by_cases hend : a + 1 + len = C + (encodeClauses φ).length
    · wram_exec [hf.fits_le, hf.dBase_eq, hj, hla, hlen, hf.one_eq, hf.cEnd_eq, hf.cBeg_eq]
      wram_call (incDLoop_spec u _ (by imp_frame hf) (by wram_simp; omega)
        (fun a' h => hA a' (by simp [h])) (by wram_simp; ram_keep hlu))
        with z ⟨hzf, hzm, hzs, hzn⟩
      wram_simp at hzm hzs
      refine ⟨by simp; omega, hzf,
        fun a' ha' => (hzm a' (by omega)).trans (by wram_simp), ?_, ?_⟩
      · intro u' h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          hhead] at h
        obtain ⟨u'', hu'', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hzj', hzl⟩ := hzs u'' hu''
        exact ⟨hzj', holdsList_cons_iff.mpr ⟨(hzm _ (by omega)).trans (by wram_simp), hzl⟩⟩
      · intro h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          Option.map_eq_none_iff] at h
        exact hzn h
    · wram_exec [hf.fits_le, hf.dBase_eq, hj, hla, hlen, hf.one_eq, hf.cEnd_eq, hf.s_eq]
      refine WP.of_execWithin
        (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, hf.s_eq]; omega)) ?_
      refine ⟨by simp only [List.length_cons]; omega, by imp_frame hf,
        fun a' ha' => by wram_simp, ?_, ?_⟩
      · intro u' h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          Option.some.injEq] at h
        subst h
        exact ⟨by wram_simp, holdsList_cons_iff.mpr ⟨by wram_simp, by wram_simp; ram_keep hlu⟩⟩
      · intro h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          reduceCtorEq] at h

/-- **Step the clause odometer** on a choice `t` of `s` clause addresses in `D`: if the odometer
step on `t` has a result, `D` holds it and `contO = 1`; if not, `contO = 0`. The memory outside
`D` is unchanged, within `12 s + 4` instructions. -/
theorem incD_spec (t : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) (hl : HoldsList Db t y.mem) :
    ∃ z, ExecWithin w incD y z (12 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + s ≤ a → z.mem a = y.mem a) ∧
      (∀ t', nextSection (List.replicate s (clauseAddrs C φ)) t = some t' →
        z.regs contO = 1 ∧ HoldsList Db t' z.mem) ∧
      (nextSection (List.replicate s (clauseAddrs C φ)) t = none → z.regs contO = 0) := by
  obtain ⟨hlen, hA⟩ := mem_sections_replicate.mp ht
  refine odometer_step_spec (by decide) hf ?_
  obtain ⟨z, hz, hzf, hzm, hzs, hzn⟩ := incDLoop_spec t (y.set jR 0) (hf.set (by decide) 0)
    (by simp [hlen]) hA (by simpa using hl)
  simp only [Data.set_regs, Function.update_self, Nat.add_zero, hlen] at hz hzm hzs hzn
  exact ⟨z, hz, hzf, hzm, hzs, hzn⟩

end ClauseOdometer

/-! ### The literal odometer -/

/-- The addresses of the literal codes of the clause stored at address `p`. -/
def litAddrs (C : ℕ) (φ : CNF (Fin n)) (p : ℕ) : List ℕ :=
  List.range' (p + 1) (clauseOf C φ p).length

/-- Set `E[j]` to the first literal address of the clause `D[j]`, and clear `sat` if that clause
is empty. -/
def initEBody : Code .standard 32 := ram[
  adr ← dBase + jR; dv ← *adr; lenR ← *dv;
  if lenR = zero then [ sat ← zero ] else [ sat ← sat ];
  dv ← dv + one; adr ← eBase + jR; *adr ← dv; jR ← jR + one ]

/-- Start `E[j], …, E[s - 1]`. -/
def initELoop : Code .standard 32 := .loop (.lt jR sReg) initEBody

/-- **Start the literal odometer**: every entry of `E` is the first literal address of its clause,
and `sat = 1` exactly when no chosen clause is empty. -/
def initE : Code .standard 32 := ram[ sat ← one; jR ← zero; ⟪initELoop⟫ ]

/-- Advance `E[j]` to the next literal address of the clause `D[j]`, or, after its last literal,
return it to the first one and carry into `E[j + 1]`. Without a carry, `jR` becomes `s + 1` and
the loop stops. -/
def incEBody : Code .standard 32 := ram[
  adr ← eBase + jR; ev ← *adr; ev ← ev + one; dv ← dBase + jR; dv ← *dv; lenR ← *dv;
  stop ← dv + one; stop ← stop + lenR;
  if ev = stop then [ ev ← dv + one; *adr ← ev; jR ← jR + one ]
  else [ *adr ← ev; jR ← sReg + one ] ]

/-- The carries of the literal odometer from `E[j]` on. -/
def incELoop : Code .standard 32 := .loop (.lt jR sReg) incEBody

/-- **Step the literal odometer**: `contI` becomes `0` after the last choice of literals, and `1`
otherwise. -/
def incE : Code .standard 32 := ram[ jR ← zero; ⟪incELoop⟫; contI ← jR - sReg ]

section LiteralOdometer

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The start loop of the literal odometer** from entry `j`, on the clause addresses `u` in
`D[j], …`: it stores their first literal addresses in `E[j], …` and clears `sat` if one of the
clauses is empty. The memory outside `E[j], …, E[s - 1]` is unchanged. -/
private theorem initELoop_spec : ∀ (u : List ℕ) (f : Bool) (y : Data 32),
    ImpFrame w φ τ x b C Tb s Db y → y.regs jR + u.length = s →
    (∀ a ∈ u, a ∈ clauseAddrs C φ) → HoldsList (Db + y.regs jR) u y.mem →
    y.regs sat = f.toNat →
    ∃ z, ExecWithin w initELoop y z (12 * u.length + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s + y.regs jR ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      HoldsList (Db + s + y.regs jR) (u.map (· + 1)) z.mem ∧
      HoldsList (Db + y.regs jR) u z.mem ∧
      z.regs sat = (f && u.all fun a => (clauseOf C φ a).length != 0).toNat
  | [], f, y, hf, hd, _, _, hs => by
    simp only [List.length_nil, Nat.add_zero] at hd
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun _ _ => rfl,
      by simp [holdsList_nil], by simp [holdsList_nil], by simpa using hs⟩
  | a :: u, f, y, hf, hd, hA, hl, hs => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd hl ⊢
    obtain ⟨hc, haA, hb_hi, hla, hlu, hlen⟩ := clauseCons_step hf j hj hd hA hl
    simp only [List.length_cons] at hd
    have hcl_le := hf.clauses_le
    set len := (clauseOf C φ a).length with hlen_def
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    refine WP.cut (fun y₁ t => t ≤ 10 ∧ ImpFrame w φ τ x b C Tb s Db y₁ ∧
      y₁.regs jR = j + 1 ∧ y₁.regs sat = (f && len != 0).toNat ∧
      y₁.mem (Db + s + j) = a + 1 ∧ ∀ a', a' ≠ Db + s + j → y₁.mem a' = y.mem a') ?_ ?_
    · unfold initEBody
      wram_exec [hf.fits_le, hf.dBase_eq, hj, hla, hlen, hf.zero_eq, hf.one_eq, hf.eBase_eq, hs]
      · exact ⟨by imp_frame hf, by wram_simp, by wram_simp; simp [hc],
          by wram_simp, fun a' ha' => by wram_simp⟩
      · exact ⟨by imp_frame hf, by wram_simp,
          by wram_simp; simp [bne_iff_ne.mpr hc],
          by wram_simp, fun a' ha' => by wram_simp⟩
    · rintro y₁ t₁ ⟨ht₁, hy₁, hj₁, hs₁, hmem_self, hy₁m⟩
      wram_call (initELoop_spec u (f && len != 0) y₁ hy₁ (by rw [hj₁]; omega)
        (fun a' h => hA a' (by simp [h])) (by rw [hj₁]; ram_keep hlu using hy₁m) hs₁)
        with z ⟨hzf, hzm, hze, hzd, hzs⟩
      rw [hj₁] at hzm hze hzd
      refine ⟨by simp only [List.length_cons]; omega, hzf,
        fun a' ha' => (hzm a' (by omega)).trans (hy₁m a' (by omega)), ?_, ?_, ?_⟩
      · rw [List.map_cons, holdsList_cons_iff]
        exact ⟨(hzm _ (by omega)).trans hmem_self, by simpa [Nat.add_assoc] using hze⟩
      · rw [holdsList_cons_iff]
        exact ⟨(hzm _ (by omega)).trans ((hy₁m _ (by omega)).trans hla),
          by simpa [Nat.add_assoc] using hzd⟩
      · rw [hzs, List.all_cons, Bool.and_assoc]

/-- **Start the literal odometer** on a choice `t` of `s` clause addresses in `D`: `E` holds their
first literal addresses, `sat = 1` exactly when none of the clauses is empty, `D` is kept, and the
memory outside `E` is unchanged, within `12 s + 4` instructions. -/
theorem initE_spec (t : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) (hl : HoldsList Db t y.mem) :
    ∃ z, ExecWithin w initE y z (12 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      HoldsList (Db + s) (t.map (· + 1)) z.mem ∧
      z.regs sat = (t.all fun a => (clauseOf C φ a).length != 0).toNat := by
  obtain ⟨hlen, hA⟩ := mem_sections_replicate.mp ht
  unfold initE
  wram_exec [hf.one_eq, hf.zero_eq]
  wram_call (initELoop_spec t true _ (by imp_frame hf) (by wram_simp [hlen]) hA
    (by wram_simp; exact hl) (by wram_simp; rfl))
    with z ⟨hzf, hzm, hze, -, hzs⟩
  wram_simp at hzm hze
  simp only [Bool.true_and] at hzs
  exact ⟨by omega, hzf, hzm, hze, hzs⟩

/-- **The carry loop of the literal odometer** from entry `j`, on clause addresses `du` in
`D[j], …` and a choice `eu` of one literal address of each in `E[j], …`: if the odometer step on
`eu` has a result, `E[j], …` holds it and `jR = s + 1`; if not, `jR = s`. The memory outside
`E[j], …, E[s - 1]` is unchanged. -/
private theorem incELoop_spec : ∀ (du eu : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs jR + du.length = s → (∀ a ∈ du, a ∈ clauseAddrs C φ) →
    HoldsList (Db + y.regs jR) du y.mem → HoldsList (Db + s + y.regs jR) eu y.mem →
    eu ∈ (du.map (litAddrs C φ)).sections →
    ∃ z, ExecWithin w incELoop y z (14 * du.length + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s + y.regs jR ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      (∀ eu', nextSection (du.map (litAddrs C φ)) eu = some eu' →
        z.regs jR = s + 1 ∧ HoldsList (Db + s + y.regs jR) eu' z.mem) ∧
      (nextSection (du.map (litAddrs C φ)) eu = none → z.regs jR = s)
  | [], eu, y, hf, hd, _, _, _, he => by
    simp only [List.length_nil, Nat.add_zero] at hd
    simp only [List.map_nil, List.sections, List.mem_singleton] at he
    subst he
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    refine ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun _ _ => rfl, ?_, ?_⟩
    · intro eu' h; simp [nextSection] at h
    · intro _; exact hd
  | a :: du, eu, y, hf, hd, hA, hl, hle, he => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd hl hle ⊢
    obtain ⟨hc, haA, hb_hi, hla, hlu, hlen⟩ := clauseCons_step hf j hj hd hA hl
    simp only [List.length_cons] at hd
    simp only [List.map_cons, List.sections, List.mem_flatMap, List.mem_map] at he
    obtain ⟨eu₀, he₀, e, hea, rfl⟩ := he
    obtain ⟨hle₀, hleu⟩ := holdsList_cons_iff.mp hle
    have hcl_le := hf.clauses_le
    set len := (clauseOf C φ a).length with hlen_def
    have hea' : a + 1 ≤ e ∧ e < a + 1 + len := by simpa [litAddrs, List.mem_range'_1] using hea
    have hsucc : succIn (litAddrs C φ a) e = if e + 1 = a + 1 + len then none else some (e + 1) :=
      succIn_range' hea
    have hhead : (litAddrs C φ a).headD 0 = a + 1 := by
      simp only [litAddrs]
      rcases hlz : len with _ | k
      · omega
      · rw [← hlen_def, hlz, List.range'_succ]; rfl
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold incEBody
    by_cases hend : e + 1 = a + 1 + len
    · wram_exec [hf.fits_le, hf.eBase_eq, hf.dBase_eq, hj, hle₀, hla, hlen, hf.one_eq]
      wram_call (incELoop_spec du eu₀ _ (by imp_frame hf) (by wram_simp; omega)
        (fun a' h => hA a' (by simp [h]))
        (by wram_simp; ram_keep hlu)
        (by
          wram_simp
          simpa [Nat.add_assoc] using (by ram_keep hleu : HoldsList (Db + s + j + 1) eu₀ _))
        he₀)
        with z ⟨hzf, hzm, hzs, hzn⟩
      wram_simp at hzm hzs
      refine ⟨by simp only [List.length_cons]; omega, hzf,
        fun a' ha' => (hzm a' (by omega)).trans (by wram_simp), ?_, ?_⟩
      · intro eu' h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte, hhead] at h
        obtain ⟨eu'', hu'', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hzj', hzl⟩ := hzs eu'' hu''
        exact ⟨hzj', holdsList_cons_iff.mpr ⟨(hzm _ (by omega)).trans (by wram_simp),
          by simpa [Nat.add_assoc] using hzl⟩⟩
      · intro h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte,
          Option.map_eq_none_iff] at h
        exact hzn h
    · wram_exec [hf.fits_le, hf.eBase_eq, hf.dBase_eq, hj, hle₀, hla, hlen, hf.one_eq, hf.s_eq]
      refine WP.of_execWithin
        (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, hf.s_eq]; omega)) ?_
      refine ⟨by simp only [List.length_cons]; omega, by imp_frame hf,
        fun a' ha' => by wram_simp, ?_, ?_⟩
      · intro eu' h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨by wram_simp, holdsList_cons_iff.mpr ⟨by wram_simp, by wram_simp; ram_keep hleu⟩⟩
      · intro h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte, reduceCtorEq] at h

/-- **Step the literal odometer** on clause addresses `t` in `D` and a choice `e` of one literal
address of each in `E`: if the odometer step on `e` has a result, `E` holds it and `contI = 1`; if
not, `contI = 0`. The memory outside `E` is unchanged, within `14 s + 4` instructions. -/
theorem incE_spec (t e : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) (hl : HoldsList Db t y.mem)
    (hle : HoldsList (Db + s) e y.mem) (he : e ∈ (t.map (litAddrs C φ)).sections) :
    ∃ z, ExecWithin w incE y z (14 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      (∀ e', nextSection (t.map (litAddrs C φ)) e = some e' →
        z.regs contI = 1 ∧ HoldsList (Db + s) e' z.mem) ∧
      (nextSection (t.map (litAddrs C φ)) e = none → z.regs contI = 0) := by
  obtain ⟨hlen, hA⟩ := mem_sections_replicate.mp ht
  refine odometer_step_spec (by decide) hf ?_
  obtain ⟨z, hz, hzf, hzm, hzs, hzn⟩ := incELoop_spec t e (y.set jR 0) (hf.set (by decide) 0)
    (by simp [hlen]) hA (by simpa using hl) (by simpa using hle) he
  simp only [Data.set_regs, Function.update_self, Nat.add_zero, hlen] at hz hzm hzs hzn
  exact ⟨z, hz, hzf, hzm, hzs, hzn⟩

end LiteralOdometer

/-! ### The compatibility test -/

/-- Compare the literal code at `E[k]` with `auxR`, the code of the complementary literal, and
clear `sat` if they are equal. -/
def pairBody : Code .standard 32 := ram[
  adr ← eBase + kR; ev ← *adr; ev ← *ev; if ev = auxR then [ sat ← zero ] else [ sat ← sat ];
  kR ← kR + one ]

/-- Compare the literal codes at `E[k], …, E[s - 1]` with `auxR`. -/
def pairLoop : Code .standard 32 := .loop (.lt kR sReg) pairBody

/-- Read the literal code at `E[j]` and clear `sat` if the literal is falsified: on `x` when its
sign is `b`, and elsewhere when the partial assignment sets its variable to the other sign. -/
def litHead : Code .standard 32 := ram[
  adr ← eBase + jR; dv ← *adr; litR ← *dv; auxR ← litR >>> one; sgnR ← litR &&& one;
  if auxR = xReg then [ if sgnR = bReg then [ sat ← zero ] else [ sat ← sat ] ]
  else [ adr ← tBase + auxR; lenR ← *adr; stop ← one - sgnR;
    if lenR = stop then [ sat ← zero ] else [ sat ← sat ] ] ]

/-- Test the literal at `E[j]`: it is not falsified, and no literal of `E` is its complement. -/
def litTest : Code .standard 32 := ram[
  ⟪litHead⟫; auxR ← litR ^^^ one; kR ← zero; ⟪pairLoop⟫; jR ← jR + one ]

/-- Test the literals at `E[j], …, E[s - 1]`. -/
def goodLoop : Code .standard 32 := .loop (.lt jR sReg) litTest

/-- **The compatibility test**: `sat = 1` exactly when the literals at the addresses in `E` are
compatible with the partial assignment with `x` set to `!b`. -/
def goodTest : Code .standard 32 := ram[ sat ← one; jR ← zero; ⟪goodLoop⟫ ]

/-- The code of the complementary literal stays below `2 n`. -/
theorem xor_one_lt {c m : ℕ} (h : c < 2 * m) : c ^^^ 1 < 2 * m := by
  rcases Nat.even_or_odd c with he | ho
  · rw [Nat.xor_one_of_even he]
    obtain ⟨k, rfl⟩ := he
    omega
  · rw [Nat.xor_one_of_odd ho]
    omega

section Compat

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The comparison loop** from entry `k`, on literal addresses `u` in `E[k], …`: `sat` is
cleared if one of their codes is `auxR`. The memory is unchanged. -/
private theorem pairLoop_spec (cc : ℕ) : ∀ (u : List ℕ) (f : Bool) (y : Data 32),
    ImpFrame w φ τ x b C Tb s Db y → y.regs kR + u.length = s →
    HoldsList (Db + s + y.regs kR) u y.mem → y.regs sat = f.toNat → y.regs auxR = cc →
    ∃ z, ExecWithin w pairLoop y z (9 * u.length + 2) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      z.regs sat = (f && (u.map y.mem).all (· != cc)).toNat
  | [], f, y, hf, hd, _, hs, _ => by
    simp only [List.length_nil, Nat.add_zero] at hd
    have hc : ¬(Cond.lt kR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), rfl, hf, by simpa using hs⟩
  | e :: u, f, y, hf, hd, hl, hs, hcc => by
    obtain ⟨k, hk⟩ : ∃ k, y.regs kR = k := ⟨_, rfl⟩
    rw [hk] at hd hl
    simp only [List.length_cons] at hd
    have hc : (Cond.lt kR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq, hk]; omega
    obtain ⟨hle, hlu⟩ := holdsList_cons_iff.mp hl
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    refine WP.cut (fun y₁ t => t ≤ 7 ∧ ImpFrame w φ τ x b C Tb s Db y₁ ∧
      y₁.mem = y.mem ∧ y₁.regs kR = k + 1 ∧ y₁.regs auxR = cc ∧
      y₁.regs sat = (f && y.mem e != cc).toNat) ?_ ?_
    · unfold pairBody
      wram_exec [hf.fits_le, hf.eBase_eq, hk, hle, hcc, hf.zero_eq, hf.one_eq, hs]
      · exact ⟨by imp_frame hf, rfl, by wram_simp, by wram_simp [hcc],
          by wram_simp; simp [hc]⟩
      · exact ⟨by imp_frame hf, rfl, by wram_simp, by wram_simp [hcc],
          by wram_simp; simp [bne_iff_ne.mpr hc]⟩
    · rintro y₁ t₁ ⟨ht₁, hy₁, hy₁m, hk₁, hcc₁, hs₁⟩
      wram_call (pairLoop_spec cc u (f && y.mem e != cc) y₁ hy₁ (by rw [hk₁]; omega)
        (by rw [hk₁, hy₁m]; simpa [Nat.add_assoc] using hlu) hs₁ hcc₁)
        with z ⟨hzm, hzf, hzs⟩
      refine ⟨by simp only [List.length_cons]; omega, hzm.trans hy₁m, hzf, ?_⟩
      rw [hzs, hy₁m]
      simp only [List.map_cons, List.all_cons, Bool.and_assoc]

/-- **The test of one literal** at `E[j]`, with code `c`: `sat` is cleared if the literal is
falsified or the code of its complement occurs in `E`. The memory is unchanged. -/
private theorem litTest_spec (El : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (hj : y.regs jR < s) (hEl : HoldsList (Db + s) El y.mem) (hlen : El.length = s)
    (hcodes : ∀ p ∈ El, y.mem p < 2 * n) (f : Bool) (hs : y.regs sat = f.toNat) :
    ∃ z, ExecWithin w litTest y z (9 * s + 20) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧ z.regs jR = y.regs jR + 1 ∧
      z.regs sat = (f && (litFine (fun v => y.mem (Tb + v)) x b.toNat
        (y.mem (El[y.regs jR]'(by omega))) &&
        (El.map y.mem).all (· != y.mem (El[y.regs jR]'(by omega)) ^^^ 1))).toNat := by
  obtain ⟨j, hjj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
  simp only [hjj] at hj ⊢
  set p := El[j]'(by omega) with hp
  have hpE : y.mem (Db + s + j) = p := hEl.get j (by omega)
  set c := y.mem p with hc_def
  have hcl : c < 2 * n := hcodes p (List.getElem_mem _)
  have hvar : c >>> 1 < n := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hsgn : c &&& 1 ≤ 1 := Nat.and_le_right
  have hst_le := hf.stored_le
  have hcd_le := hf.codes_le
  have hxor_lt := xor_one_lt hcl
  set F := (f && litFine (fun v => y.mem (Tb + v)) x b.toNat c).toNat with hF
  obtain ⟨y₁, hy₁, hy₁f, hy₁m, hy₁s, hy₁l, hy₁j⟩ : ∃ y₁, ExecWithin w litHead y y₁ 13 ∧
      ImpFrame w φ τ x b C Tb s Db y₁ ∧ y₁.mem = y.mem ∧ y₁.regs sat = F ∧ y₁.regs litR = c ∧
      y₁.regs jR = j := by
    unfold litHead
    wram_exec [hf.fits_le, hf.eBase_eq, hjj, hpE, ← hc_def, hf.one_eq, hf.x_eq, hf.b_eq,
      hf.tBase_eq, hf.zero_eq, hs]
    · rename_i hvar_eq
      exact ⟨by imp_frame hf, rfl, by
        wram_simp
        simp only [F, litFine, hvar_eq, hc, ↓reduceIte, bne_self_eq_false, Bool.and_false]
        rfl,
        by wram_simp, by wram_simp [hjj]⟩
    · rename_i hvar_eq
      exact ⟨by imp_frame hf, rfl, by
        wram_simp
        simp only [F, litFine, hvar_eq, bne_iff_ne.mpr hc, ↓reduceIte, Bool.and_true],
        by wram_simp, by wram_simp [hjj]⟩
    · rename_i hvar_eq
      exact ⟨by imp_frame hf, rfl, by
        wram_simp
        simp only [F, litFine, hvar_eq, hc, ↓reduceIte, bne_self_eq_false, Bool.and_false]
        rfl,
        by wram_simp, by wram_simp [hjj]⟩
    · rename_i hvar_eq
      exact ⟨by imp_frame hf, rfl, by
        wram_simp
        simp only [F, litFine, hvar_eq, bne_iff_ne.mpr hc, ↓reduceIte, Bool.and_true],
        by wram_simp, by wram_simp [hjj]⟩
  unfold litTest
  refine WP.exists_execWithin (WP.seq (WP.of_execWithin hy₁ ?_))
  wram_exec [hy₁f.fits_le, hy₁l, hy₁f.one_eq, hy₁f.zero_eq]
  refine WP.name fun y₂ hy₂ => ?_
  obtain ⟨z₃, hz₃, hz₃m, hz₃f, hz₃s⟩ :=
    pairLoop_spec (c ^^^ 1) El (F == 1) y₂ (by subst hy₂; imp_frame hy₁f)
      (by subst hy₂; wram_simp [hlen]) (by subst hy₂; wram_simp [hy₁m]; exact hEl)
      (by
        subst hy₂; wram_simp [hy₁s, hF]
        cases (f && litFine (fun v => y.mem (Tb + v)) x b.toNat c) <;> rfl)
      (by subst hy₂; wram_simp)
  have hj₃ : z₃.regs jR = j := (hz₃.regs_eq (by decide)).trans (by subst hy₂; wram_simp [hy₁j])
  have hy₂m : y₂.mem = y.mem := by subst hy₂; exact hy₁m
  refine WP.of_execWithin hz₃ ?_
  wram_exec [hz₃f.fits_le, hj₃, hz₃f.one_eq]
  refine ⟨by wram_simp [hz₃m, hy₂m], by imp_frame hz₃f, by wram_simp, ?_⟩
  wram_simp [hz₃s, hy₂m, hF]
  simp only [← Bool.and_assoc, List.all_map]
  cases (f && litFine (fun v => y.mem (Tb + v)) x b.toNat c) <;> rfl

end Compat

section Good

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The loop of the compatibility test** from entry `j`, on the literal addresses
`u = E[j], …` of the full list `El` in `E`. The memory is unchanged. -/
private theorem goodLoop_spec (El : List ℕ) (hlen : El.length = s) : ∀ (u : List ℕ) (f : Bool)
    (y : Data 32), ImpFrame w φ τ x b C Tb s Db y → u = El.drop (y.regs jR) →
    y.regs jR ≤ s → HoldsList (Db + s) El y.mem → (∀ p ∈ El, y.mem p < 2 * n) →
    y.regs sat = f.toNat →
    ∃ z, ExecWithin w goodLoop y z (u.length * (9 * s + 22) + 2) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      z.regs sat = (f && u.all fun p => litFine (fun v => y.mem (Tb + v)) x b.toNat (y.mem p) &&
        (El.map y.mem).all (· != y.mem p ^^^ 1)).toNat
  | [], f, y, hf, hu, hj, _, _, hs => by
    have hj' : s ≤ y.regs jR := by
      have := congrArg List.length hu; simp at this; omega
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), rfl, hf, by simpa using hs⟩
  | p :: u, f, y, hf, hu, hj, hEl, hcodes, hs => by
    have hjs : y.regs jR < s := by
      have := congrArg List.length hu; simp at this; omega
    rw [List.drop_eq_getElem_cons (by omega), List.cons.injEq] at hu
    obtain ⟨hp, hu⟩ := hu
    have hc : (Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    obtain ⟨z₁, hz₁, hz₁m, hz₁f, hz₁j, hz₁s⟩ := litTest_spec El y hf hjs hEl hlen hcodes f hs
    obtain ⟨z, hz, hzm, hzf, hzs⟩ := goodLoop_spec El hlen u _ z₁ hz₁f
      (by rw [hz₁j]; exact hu) (by omega) (by rw [hz₁m]; exact hEl)
      (by rw [hz₁m]; exact hcodes) hz₁s
    refine ⟨z, (ExecWithin.loop_iter hc hz₁ hz).mono (by simp only [List.length_cons]; nlinarith),
      by rw [hzm, hz₁m], hzf, ?_⟩
    rw [hzs, hz₁m, ← hp, List.all_cons, Bool.and_assoc]

/-- The time of the compatibility test on `s` literals. -/
def goodTime (s : ℕ) : ℕ := s * (9 * s + 22) + 4

/-- **The compatibility test**: `sat = 1` exactly when the literal codes at the addresses `El` in
`E` are compatible (`compatCodes`), within `goodTime s` instructions. The memory is unchanged. -/
theorem goodTest_spec (El : List ℕ) (hlen : El.length = s) (y : Data 32)
    (hf : ImpFrame w φ τ x b C Tb s Db y) (hEl : HoldsList (Db + s) El y.mem)
    (hcodes : ∀ p ∈ El, y.mem p < 2 * n) :
    ∃ z, ExecWithin w goodTest y z (goodTime s) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      z.regs sat = (compatCodes (fun v => y.mem (Tb + v)) x b.toNat (El.map y.mem)).toNat := by
  unfold goodTest
  wram_exec [hf.one_eq, hf.zero_eq]
  wram_call (goodLoop_spec El hlen El true _ (by imp_frame hf) (by wram_simp; rfl)
    (by wram_simp; omega) (by wram_simp; exact hEl) (by wram_simp; exact hcodes)
    (by wram_simp; rfl))
    with z ⟨hzm, hzf, hzs⟩
  refine ⟨by simp only [goodTime, hlen]; omega, hzm, hzf, ?_⟩
  rw [hzs]
  simp only [Data.set_mem, Bool.true_and, compatCodes, List.all_map, Function.comp_def]

end Good

/-! ### Sections: shape and size -/

/-- With an empty list among `L`, there is no section. -/
theorem sections_eq_nil_of_nil_mem {α : Type*} : ∀ {L : List (List α)}, [] ∈ L → L.sections = []
  | [], h => by simp at h
  | l :: L, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simp [sections_eq_nil_of_nil_mem h]

/-- Without an empty list among `L`, the first section picks the first entry of every list. -/
theorem sections_eq_cons_headD {α : Type*} (d : α) : ∀ {L : List (List α)},
    (∀ l ∈ L, l ≠ []) → ∃ xs, L.sections = L.map (·.headD d) :: xs
  | [], _ => ⟨[], rfl⟩
  | l :: L, h => by
    obtain ⟨xs, hxs⟩ := sections_eq_cons_headD d (L := L) fun l' hl' =>
      h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil (h l (by simp))
    refine ⟨l'.map (· :: L.map (·.headD d)) ++ xs.flatMap (fun t => (a :: l').map (· :: t)), ?_⟩
    simp only [List.sections, hxs, List.flatMap_cons, List.map_cons, List.cons_append,
      List.headD_cons]

/-- The number of sections of lists of length at most `m`. -/
theorem length_sections_le {α : Type*} {m : ℕ} : ∀ {L : List (List α)},
    (∀ l ∈ L, l.length ≤ m) → L.sections.length ≤ m ^ L.length
  | [], _ => by simp
  | l :: L, h => by
    have ih := length_sections_le (L := L) fun l' hl' => h l' (by simp [hl'])
    simp only [List.sections, List.length_flatMap, List.length_map, List.length_cons, pow_succ]
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    have := h l (by simp)
    calc L.sections.length * l.length ≤ m ^ L.length * m := Nat.mul_le_mul ih this

/-- `List.all` depends only on the values of the test on the list. -/
theorem all_congr_of_mem {α : Type*} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- Compatibility through codes reads only the codes and the words of their variables. -/
private theorem compatCodes_congr {m₁ m₂ : ℕ → ℕ} {Tb x b : ℕ} {El : List ℕ}
    (hE : ∀ p ∈ El, m₁ p = m₂ p) (hc : ∀ p ∈ El, m₁ p < 2 * n)
    (hτ : ∀ v < n, m₁ (Tb + v) = m₂ (Tb + v)) :
    compatCodes (fun v => m₁ (Tb + v)) x b (El.map m₁) =
      compatCodes (fun v => m₂ (Tb + v)) x b (El.map m₂) := by
  rw [← List.map_congr_left hE]
  unfold compatCodes
  refine all_congr_of_mem fun c hc' => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
  have hv : m₁ p >>> 1 < n := by rw [Nat.shiftRight_eq_div_pow]; have := hc p hp; omega
  simp only [litFine, hτ _ hv]

/-- The literal addresses of a clause address hold literal codes, below `2 n`. -/
private theorem mem_litAddr_lt {mem : ℕ → ℕ} {C : ℕ} {φ : CNF (Fin n)}
    (hφ : HoldsList C (encodeClauses φ) mem) {a : ℕ} (ha : a ∈ clauseAddrs C φ) {p : ℕ}
    (hp : p ∈ litAddrs C φ a) : mem p < 2 * n := by
  have hc := holdsList_clauseOf hφ ha
  simp only [litAddrs, List.mem_range'_1] at hp
  obtain ⟨i, rfl⟩ : ∃ i, p = a + 1 + i := ⟨p - (a + 1), by omega⟩
  have := hc.get (i + 1) (by simp [encodeClause]; omega)
  rw [show a + (i + 1) = a + 1 + i by omega] at this
  rw [this]
  simp only [encodeClause, List.getElem_cons_succ, List.getElem_map]
  exact litCode_lt _

/-- The literal addresses of a clause address lie in the encoding of the clauses. -/
theorem lt_of_mem_litAddrs {C : ℕ} {φ : CNF (Fin n)} {a : ℕ} (ha : a ∈ clauseAddrs C φ) {p : ℕ}
    (hp : p ∈ litAddrs C φ a) : p < C + (encodeClauses φ).length := by
  have := bounds_of_mem_clauseAddrs ha
  simp only [litAddrs, List.mem_range'_1] at hp
  omega

/-- The literal addresses of a clause are duplicate-free. -/
private theorem litAddrs_nodup (C : ℕ) (φ : CNF (Fin n)) (a : ℕ) : (litAddrs C φ a).Nodup :=
  List.nodup_range'

/-- A clause has at most as many literals as the encoding has words. -/
theorem length_litAddrs_le {C : ℕ} {φ : CNF (Fin n)} {a : ℕ} (ha : a ∈ clauseAddrs C φ) :
    (litAddrs C φ a).length ≤ (encodeClauses φ).length := by
  have := bounds_of_mem_clauseAddrs ha
  simp only [litAddrs, List.length_range']
  omega

/-- There are at most as many clauses as the encoding has words. -/
theorem length_clauseAddrs_le : ∀ (a : ℕ) (φ : CNF (Fin n)),
    (clauseAddrs a φ).length ≤ (encodeClauses φ).length
  | _, [] => by simp [clauseAddrs]
  | a, c :: φ => by
    have := length_clauseAddrs_le (a + 1 + c.length) φ
    simp only [clauseAddrs, List.length_cons, encodeClauses_cons, List.length_append,
      length_encodeClause]
    omega

/-! ### The search over choices of literals -/

/-- One step of the literal search: test the current choice, and stop if it is compatible;
otherwise step the odometer. -/
def innerBody : Code .standard 32 := ram[
  ⟪goodTest⟫; if sat = one then [ contI ← zero ] else [ ⟪incE⟫ ] ]

/-- The literal search from the current choice on. -/
def innerLoop : Code .standard 32 := .loop (.lt zero contI) innerBody

/-- **The literal search**: `sat = 1` exactly when some choice of one literal address from each
clause in `D` is compatible. -/
def innerSearch : Code .standard 32 := ram[
  ⟪initE⟫; if sat = one then [ contI ← one; ⟪innerLoop⟫ ] else [ sat ← sat ] ]

/-- The time of one step of the literal search. -/
def innerIter (s : ℕ) : ℕ := goodTime s + 14 * s + 9

/-- The time of the literal search, with at most `E ^ s` choices of literals. -/
def innerTime (s E : ℕ) : ℕ := 12 * s + 8 + E ^ s * innerIter s

section Inner

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The test of the literal search, on the memory `m`. -/
def litOk (m : ℕ → ℕ) (Tb : ℕ) (x : Fin n) (b : Bool) (e : List ℕ) : Bool :=
  compatCodes (fun v => m (Tb + v)) x b.toNat (e.map m)

private theorem mem_litAddrs_of_mem_sections {C : ℕ} {φ : CNF (Fin n)} {t e : List ℕ}
    (he : e ∈ (t.map (litAddrs C φ)).sections) {p : ℕ} (hp : p ∈ e) :
    ∃ a ∈ t, p ∈ litAddrs C φ a := by
  have h2 := List.mem_sections.mp he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have := (List.forall₂_iff_get.mp h2).2 i hi (by simpa [← h2.length_eq] using hi)
  simp only [List.get_eq_getElem, List.getElem_map] at this
  exact ⟨_, List.getElem_mem _, this⟩

/-- The test of the literal search reads only memory below `Db`. -/
theorem litOk_congr {t : List ℕ} (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections)
    {m₁ m₂ : ℕ → ℕ} (hcl : HoldsList C (encodeClauses φ) m₁)
    (hle : C + (encodeClauses φ).length ≤ Db) (hTb : Tb + n ≤ Db) (hm : ∀ a < Db, m₂ a = m₁ a)
    {e : List ℕ} (he : e ∈ (t.map (litAddrs C φ)).sections) :
    litOk m₂ Tb x b e = litOk m₁ Tb x b e := by
  obtain ⟨-, htA⟩ := mem_sections_replicate.mp ht
  have hlt : ∀ p ∈ e, p < Db := fun p hp => by
    obtain ⟨a, ha, hpa⟩ := mem_litAddrs_of_mem_sections he hp
    have := lt_of_mem_litAddrs (htA a ha) hpa
    omega
  refine compatCodes_congr (n := n) (fun p hp => hm p (hlt p hp)) (fun p hp => ?_)
    (fun v hv => hm _ (by omega))
  rw [hm p (hlt p hp)]
  obtain ⟨a, ha, hpa⟩ := mem_litAddrs_of_mem_sections he hp
  exact mem_litAddr_lt hcl (htA a ha) hpa

/-- **The loop of the literal search**, on the clause addresses `t` in `D`, from the choice `e`
in `E`, followed by the choices `xs`: `sat = 1` exactly when one of them is compatible. The memory
outside `E` is unchanged. -/
private theorem innerLoop_spec (t : List ℕ)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) :
    ∀ (xs : List (List ℕ)) (e : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
      HoldsList Db t y.mem → HoldsList (Db + s) e y.mem → y.regs contI = 1 →
      Enumerates (t.map (litAddrs C φ)) (e :: xs) →
      (∀ e' ∈ e :: xs, e' ∈ (t.map (litAddrs C φ)).sections) →
      ∃ z, ExecWithin w innerLoop y z ((xs.length + 1) * innerIter s + 2) ∧
        ImpFrame w φ τ x b C Tb s Db z ∧
        (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
        z.regs sat = ((e :: xs).any (litOk y.mem Tb x b)).toNat := by
  obtain ⟨htlen, htA⟩ := mem_sections_replicate.mp ht
  intro xs
  refine Nat.strongRecOn (motive := fun k => ∀ xs : List (List ℕ), xs.length = k →
    ∀ (e : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
      HoldsList Db t y.mem → HoldsList (Db + s) e y.mem → y.regs contI = 1 →
      Enumerates (t.map (litAddrs C φ)) (e :: xs) →
      (∀ e' ∈ e :: xs, e' ∈ (t.map (litAddrs C φ)).sections) →
      ∃ z, ExecWithin w innerLoop y z ((xs.length + 1) * innerIter s + 2) ∧
        ImpFrame w φ τ x b C Tb s Db z ∧
        (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
        z.regs sat = ((e :: xs).any (litOk y.mem Tb x b)).toNat)
    xs.length (fun k ih xs hk e y hf ht' he hc hen hmem => ?_) xs rfl
  have he' := hmem e (by simp)
  have hcond : (Cond.lt zero contI).Holds y := by simp [Cond.holds_lt, hf.zero_eq, hc]
  have hlen : e.length = s := by rw [List.mem_sections_length he', List.length_map, htlen]
  have hcodes : ∀ p ∈ e, y.mem p < 2 * n := fun p hp => by
    obtain ⟨a, ha, hpa⟩ := mem_litAddrs_of_mem_sections he' hp
    exact mem_litAddr_lt hf.clauses (htA a ha) hpa
  obtain ⟨z₁, hz₁, hz₁m, hz₁f, hz₁s⟩ := goodTest_spec e hlen y hf he hcodes
  replace hz₁s : z₁.regs sat = (litOk y.mem Tb x b e).toNat := hz₁s
  refine WP.exists_execWithin (WP.loop_iter hcond ?_)
  unfold innerBody
  refine WP.seq (WP.of_execWithin hz₁ ?_)
  rcases hok : litOk y.mem Tb x b e
  · -- not compatible: step the odometer
    wram_exec [hz₁s, hok, hz₁f.one_eq]
    obtain ⟨z₂, hz₂, hz₂f, hz₂m, hz₂s, hz₂n⟩ := incE_spec t e z₁ hz₁f ht
      (by rw [hz₁m]; exact ht') (by rw [hz₁m]; exact he) he'
    refine WP.of_execWithin hz₂ ?_
    rcases xs with _ | ⟨e', xs⟩
    · have hn : nextSection (t.map (litAddrs C φ)) e = none := by simpa using hen.head
      have hcz : ¬(Cond.lt zero contI).Holds z₂ := by
        simp [Cond.holds_lt, hz₂f.zero_eq, hz₂n hn]
      have hsz : z₂.regs sat = 0 := by rw [hz₂.regs_eq (by decide), hz₁s, hok]; rfl
      refine WP.of_execWithin (ExecWithin.loop_exit hcz)
        ⟨by simp only [innerIter, List.length_nil]; omega, hz₂f,
          fun a ha => by rw [hz₂m a ha, hz₁m], by simp [hsz, hok]⟩
    · have hn : nextSection (t.map (litAddrs C φ)) e = some e' := by simpa using hen.head
      obtain ⟨hc₂, he₂⟩ := hz₂s e' hn
      have ht₂ : HoldsList Db t z₂.mem := by
        have hkeep : HoldsList Db t z₁.mem := by simpa only [hz₁m] using ht'
        ram_keep hkeep using hz₂m
      wram_call (ih xs.length (by simp [← hk]) xs rfl e' z₂ hz₂f ht₂
        he₂ hc₂ hen.tail fun e'' h => hmem e'' (List.mem_cons_of_mem _ h))
        with z₃ ⟨hz₃f, hz₃m, hz₃s⟩
      have hm₃ : ∀ a < Db, z₂.mem a = y.mem a := fun a ha => by rw [hz₂m a (by omega), hz₁m]
      refine ⟨by simp only [innerIter, List.length_cons]; ring_nf; omega, hz₃f,
        fun a ha => by rw [hz₃m a ha, hz₂m a ha, hz₁m], ?_⟩
      rw [hz₃s, List.any_cons (a := e), hok, Bool.false_or]
      congr 1
      exact any_congr_of_mem fun e'' h =>
        litOk_congr ht hf.clauses hf.clauses_le hf.stored_le hm₃
          (hmem e'' (List.mem_cons_of_mem _ h))
  · -- compatible: stop
    wram_exec [hz₁s, hok, hz₁f.one_eq, hz₁f.zero_eq]
    refine WP.of_execWithin
      (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, hz₁f.zero_eq])) ?_
    have hiter : innerIter s ≤ (xs.length + 1) * innerIter s :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact ⟨by simp only [innerIter] at hiter ⊢; omega, by imp_frame hz₁f,
      fun a _ => by wram_simp [hz₁m], by wram_simp [hz₁s, hok]; simp [hok]⟩

/-- **The literal search** on a choice `t` of `s` clause addresses in `D`: `sat = 1` exactly when
some choice of one literal address from each clause is compatible, within `innerTime s E`
instructions, where `E` is the length of the encoding of the clauses. The memory outside `E` is
unchanged. -/
theorem innerSearch_spec (t : List ℕ) (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections)
    (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) (hl : HoldsList Db t y.mem) :
    ∃ z, ExecWithin w innerSearch y z (innerTime s (encodeClauses φ).length) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = ((t.map (litAddrs C φ)).sections.any (litOk y.mem Tb x b)).toNat := by
  obtain ⟨htlen, htA⟩ := mem_sections_replicate.mp ht
  have hcount : (t.map (litAddrs C φ)).sections.length ≤ (encodeClauses φ).length ^ s := by
    have := length_sections_le (m := (encodeClauses φ).length) (L := t.map (litAddrs C φ))
      (by
        intro l hl'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl'
        exact length_litAddrs_le (htA a ha))
    simpa [htlen] using this
  unfold innerSearch
  refine WP.exists_execWithin (WP.seq ?_)
  wram_call (initE_spec t y hf ht hl) with z₁ ⟨hz₁f, hz₁m, hz₁e, hz₁s⟩
  have hm₁ : ∀ a < Db, z₁.mem a = y.mem a := fun a ha => hz₁m a (by omega)
  rcases hall : t.all fun a => (clauseOf C φ a).length != 0
  · obtain ⟨a, ha, ha0⟩ : ∃ a ∈ t, (clauseOf C φ a).length = 0 := by simpa using hall
    have hnil : (t.map (litAddrs C φ)).sections = [] :=
      sections_eq_nil_of_nil_mem (List.mem_map.mpr ⟨a, ha, by simp [litAddrs, ha0]⟩)
    wram_exec [hz₁s, hall, hz₁f.one_eq]
    exact ⟨by simp only [innerTime]; nlinarith, by imp_frame hz₁f,
      fun a ha => by wram_simp [hz₁m a ha], by wram_simp [hnil]; rfl⟩
  · have hne : ∀ l ∈ t.map (litAddrs C φ), l ≠ [] := by
      intro l hl'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl'
      have := List.all_eq_true.mp hall a ha
      simp only [bne_iff_ne, ne_eq] at this
      simp [litAddrs, this]
    obtain ⟨xs, hxs⟩ := sections_eq_cons_headD 0 hne
    have hhead : (t.map (litAddrs C φ)).map (·.headD 0) = t.map (· + 1) := by
      simp only [List.map_map]
      refine List.map_congr_left fun a ha => ?_
      have := List.all_eq_true.mp hall a ha
      simp only [bne_iff_ne, ne_eq] at this
      simp only [Function.comp_apply, litAddrs]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk, List.range'_succ]
      rfl
    rw [hhead] at hxs
    have hen : Enumerates (t.map (litAddrs C φ)) (t.map (· + 1) :: xs) := by
      rw [← hxs]
      exact nextSection_sections fun l hl' => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hl'
        exact litAddrs_nodup C φ a
    wram_exec [hz₁s, hall, hz₁f.one_eq]
    wram_call (innerLoop_spec t ht xs (t.map (· + 1)) _ (by imp_frame hz₁f)
      (by wram_simp; ram_keep hl using hz₁m) (by wram_simp; exact hz₁e) (by wram_simp)
      hen (by rw [← hxs]; exact fun _ h => h))
      with z ⟨hzf, hzm, hzs⟩
    have hlen' : xs.length + 1 ≤ (encodeClauses φ).length ^ s := by
      have := congrArg List.length hxs
      simp only [List.length_cons] at this
      omega
    refine ⟨?_, hzf, fun a ha => (hzm a ha).trans (by wram_simp [hz₁m a ha]), ?_⟩
    · have := Nat.mul_le_mul_right (innerIter s) hlen'
      simp only [innerTime]
      omega
    · rw [hzs, ← hxs]
      congr 1
      exact any_congr_of_mem fun e he =>
        litOk_congr ht hf.clauses hf.clauses_le hf.stored_le hm₁ he

end Inner

/-! ### The search over choices of clauses -/

/-- One step of the clause search: search the choices of literals, and stop if none is
compatible; otherwise step the odometer. -/
def outerBody : Code .standard 32 := ram[
  ⟪innerSearch⟫; if sat = zero then [ contO ← zero ] else [ ⟪incD⟫ ] ]

/-- The clause search from the current choice on. -/
def outerLoop : Code .standard 32 := .loop (.lt zero contO) outerBody

/-- **The clause search**: `sat = 0` exactly when some choice of `s` clause addresses has no
compatible choice of literals. -/
def outerSearch : Code .standard 32 := ram[ ⟪initD⟫; contO ← one; ⟪outerLoop⟫ ]

/-- The time of one step of the clause search. -/
def outerIter (s E : ℕ) : ℕ := innerTime s E + 12 * s + 8

/-- The time of the clause search, with at most `E ^ s` choices of clauses. -/
def outerTime (s E : ℕ) : ℕ := 5 * s + 6 + E ^ s * outerIter s E

section Outer

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The test of the clause search: the clauses at the addresses `t` have a compatible choice of
literals, on the memory `m`. -/
def clauseOk (m : ℕ → ℕ) (C Tb : ℕ) (φ : CNF (Fin n)) (x : Fin n) (b : Bool) (t : List ℕ) :
    Bool :=
  (t.map (litAddrs C φ)).sections.any (litOk m Tb x b)

/-- **The loop of the clause search**, from the choice `t` in `D`, followed by the choices `xs`:
`sat = 1` exactly when each of them has a compatible choice of literals. The memory outside `D`
and `E` is unchanged. -/
private theorem outerLoop_spec : ∀ (xs : List (List ℕ)) (t : List ℕ) (y : Data 32),
    ImpFrame w φ τ x b C Tb s Db y → HoldsList Db t y.mem → y.regs contO = 1 →
    Enumerates (List.replicate s (clauseAddrs C φ)) (t :: xs) →
    (∀ t' ∈ t :: xs, t' ∈ (List.replicate s (clauseAddrs C φ)).sections) →
    ∃ z, ExecWithin w outerLoop y z
        ((xs.length + 1) * outerIter s (encodeClauses φ).length + 2) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = ((t :: xs).all (clauseOk y.mem C Tb φ x b)).toNat := by
  intro xs
  refine Nat.strongRecOn (motive := fun k => ∀ xs : List (List ℕ), xs.length = k →
    ∀ (t : List ℕ) (y : Data 32),
      ImpFrame w φ τ x b C Tb s Db y → HoldsList Db t y.mem → y.regs contO = 1 →
      Enumerates (List.replicate s (clauseAddrs C φ)) (t :: xs) →
      (∀ t' ∈ t :: xs, t' ∈ (List.replicate s (clauseAddrs C φ)).sections) →
      ∃ z, ExecWithin w outerLoop y z
          ((xs.length + 1) * outerIter s (encodeClauses φ).length + 2) ∧
        ImpFrame w φ τ x b C Tb s Db z ∧
        (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
        z.regs sat = ((t :: xs).all (clauseOk y.mem C Tb φ x b)).toNat)
    xs.length (fun k ih xs hk t y hf hl hc hen hmem => ?_) xs rfl
  have ht := hmem t (by simp)
  have hcond : (Cond.lt zero contO).Holds y := by simp [Cond.holds_lt, hf.zero_eq, hc]
  obtain ⟨z₁, hz₁, hz₁f, hz₁m, hz₁s⟩ := innerSearch_spec t ht y hf hl
  replace hz₁s : z₁.regs sat = (clauseOk y.mem C Tb φ x b t).toNat := hz₁s
  refine WP.exists_execWithin (WP.loop_iter hcond ?_)
  unfold outerBody
  refine WP.seq (WP.of_execWithin hz₁ ?_)
  rcases hok : clauseOk y.mem C Tb φ x b t
  · wram_exec [hz₁s, hok, hz₁f.zero_eq]
    refine WP.of_execWithin
      (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, hz₁f.zero_eq])) ?_
    have hiter :
        outerIter s (encodeClauses φ).length ≤
          (xs.length + 1) * outerIter s (encodeClauses φ).length :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact ⟨by simp only [outerIter] at hiter ⊢; omega, by imp_frame hz₁f,
      fun a ha => by wram_simp [hz₁m a (by omega)], by wram_simp [hz₁s, hok]; simp [hok]⟩
  · wram_exec [hz₁s, hok, hz₁f.zero_eq]
    have htlen := (mem_sections_replicate.mp ht).1
    have hl₁ : HoldsList Db t z₁.mem := by ram_keep hl using hz₁m
    obtain ⟨z₂, hz₂, hz₂f, hz₂m, hz₂s, hz₂n⟩ := incD_spec t z₁ hz₁f ht hl₁
    refine WP.of_execWithin hz₂ ?_
    have hm₁₂ : ∀ a, a < Db ∨ Db + 2 * s ≤ a → z₂.mem a = y.mem a := fun a ha => by
      rcases ha with ha | ha
      · rw [hz₂m a (Or.inl ha), hz₁m a (by omega)]
      · rw [hz₂m a (Or.inr (by omega)), hz₁m a (Or.inr ha)]
    rcases xs with _ | ⟨t', xs⟩
    · have hn : nextSection (List.replicate s (clauseAddrs C φ)) t = none := by
        simpa using hen.head
      have hcz : ¬(Cond.lt zero contO).Holds z₂ := by
        simp [Cond.holds_lt, hz₂f.zero_eq, hz₂n hn]
      have hsz : z₂.regs sat = 1 := by rw [hz₂.regs_eq (by decide), hz₁s, hok]; rfl
      exact WP.of_execWithin (ExecWithin.loop_exit hcz)
        ⟨by simp only [outerIter, List.length_nil]; omega, hz₂f, hm₁₂, by simp [hsz, hok]⟩
    · have hn : nextSection (List.replicate s (clauseAddrs C φ)) t = some t' := by
        simpa using hen.head
      obtain ⟨hc₂, hl₂⟩ := hz₂s t' hn
      wram_call (ih xs.length (by simp [← hk]) xs rfl t' z₂ hz₂f hl₂
        hc₂ hen.tail fun t'' h => hmem t'' (List.mem_cons_of_mem _ h))
        with z₃ ⟨hz₃f, hz₃m, hz₃s⟩
      refine ⟨by simp only [outerIter, List.length_cons]; ring_nf; omega, hz₃f,
        fun a ha => (hz₃m a ha).trans (hm₁₂ a ha), ?_⟩
      rw [hz₃s, List.all_cons (a := t), hok, Bool.true_and]
      congr 1
      refine all_congr_of_mem fun t'' h => ?_
      have ht'' := hmem t'' (List.mem_cons_of_mem _ h)
      exact any_congr_of_mem fun e he =>
        litOk_congr ht'' hf.clauses hf.clauses_le hf.stored_le (fun a ha => hm₁₂ a (Or.inl ha)) he

/-- **The clause search**, on a nonempty formula: `sat = 1` exactly when every choice of `s`
clause addresses has a compatible choice of literals, within `outerTime s E` instructions. The
memory outside `D` and `E` is unchanged. -/
theorem outerSearch_spec (hφ : φ ≠ []) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w outerSearch y z (outerTime s (encodeClauses φ).length) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = ((List.replicate s (clauseAddrs C φ)).sections.all
        (clauseOk y.mem C Tb φ x b)).toNat := by
  have hA : clauseAddrs C φ ≠ [] := by
    rcases φ with _ | ⟨c, φ⟩
    · exact absurd rfl hφ
    · simp [clauseAddrs]
  obtain ⟨xs, hxs⟩ := sections_eq_cons_headD 0 (L := List.replicate s (clauseAddrs C φ))
    fun l hl => by rw [List.eq_of_mem_replicate hl]; exact hA
  rw [List.map_replicate, headD_clauseAddrs hφ] at hxs
  have hen : Enumerates (List.replicate s (clauseAddrs C φ)) (List.replicate s C :: xs) := by
    rw [← hxs]
    exact nextSection_sections fun l hl => by
      rw [List.eq_of_mem_replicate hl]; exact clauseAddrs_nodup C φ
  unfold outerSearch
  refine WP.exists_execWithin (WP.seq ?_)
  wram_call (initD_spec y hf) with z₁ ⟨hz₁f, hz₁l, hz₁m⟩
  wram_exec [hz₁f.one_eq]
  wram_call (outerLoop_spec xs (List.replicate s C) _ (by imp_frame hz₁f)
    (by wram_simp; exact hz₁l) (by wram_simp) hen (by rw [← hxs]; exact fun _ h => h))
    with z ⟨hzf, hzm, hzs⟩
  have hcount : xs.length + 1 ≤ (encodeClauses φ).length ^ s := by
    have := length_sections_le (m := (encodeClauses φ).length)
      (L := List.replicate s (clauseAddrs C φ))
      (fun l hl => by rw [List.eq_of_mem_replicate hl]; exact length_clauseAddrs_le C φ)
    rw [hxs] at this
    simpa using this
  have hm₁ : ∀ a < Db, z₁.mem a = y.mem a := fun a ha => hz₁m a (Or.inl ha)
  refine ⟨?_, hzf, fun a ha => (hzm a ha).trans (by wram_simp [hz₁m a (by omega)]), ?_⟩
  · have := Nat.mul_le_mul_right (outerIter s (encodeClauses φ).length) hcount
    simp only [outerTime]
    omega
  · rw [hzs, ← hxs]
    congr 1
    refine all_congr_of_mem fun t ht => ?_
    exact any_congr_of_mem fun e he =>
      litOk_congr ht hf.clauses hf.clauses_le hf.stored_le hm₁ he

end Outer

/-! ### Deciding w-implication -/

/-- Load the word of `x` in the partial assignment. -/
def impLoad : Code .standard 32 := ram[ adr ← tBase + xReg; lenR ← *adr ]

/-- **The w-implication search** for `x = b`: `sat = 0` exactly when the partial assignment sets
`x` to `b`, or some choice of `s` clauses has no compatible choice of literals with `x` set to
`!b`. -/
def impScan : Code .standard 32 := ram[
  ⟪impLoad⟫;
  if lenR = bReg then [ sat ← zero ]
  else [ if cBeg < cEnd then [ ⟪outerSearch⟫ ] else [ sat ← one ] ] ]

/-- The time of the w-implication search. -/
def impScanTime (s E : ℕ) : ℕ := outerTime s E + 6

section Scan

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The w-implication search decides w-implication**: `sat = 0` exactly when `x = b` is
`s`-implied under `τ` (through `Cslib.Complexity.PPSZ.impliedTest`), within `impScanTime s E`
instructions. The memory outside `D` and `E` is unchanged. -/
theorem impScan_spec (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w impScan y z (impScanTime s (encodeClauses φ).length) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = (!impliedTest φ s τ x b).toNat := by
  have hTx : y.mem (Tb + x) = optCode (τ x) := hf.stored x
  have hst_le := hf.stored_le
  have htest := addrTest_eq (s := s) (x := x) (b := b) hf.clauses hf.stored
  rw [← htest]
  unfold impScan impLoad
  wram_exec -split [hf.fits_le, hf.tBase_eq, hf.x_eq, hTx]
  by_cases hτx : optCode (τ x) = b.toNat
  · wram_exec [hf.b_eq, hf.zero_eq, hτx]
    exact ⟨by simp only [impScanTime, outerTime]; omega, by imp_frame hf,
      fun _ _ => rfl, by wram_simp; simp [addrTest, hTx, hτx]⟩
  · have hfirst : (y.mem (Tb + x) == b.toNat) = false := by simp [hTx, hτx]
    rcases φ with _ | ⟨c₀, φ'⟩
    · have hc0 : (encodeClauses ([] : CNF (Fin n))).length = 0 := rfl
      wram_exec [hf.b_eq, hf.cBeg_eq, hf.cEnd_eq, hc0, hf.one_eq]
      refine ⟨by simp only [impScanTime, outerTime]; omega, by imp_frame hf,
        fun _ _ => rfl, ?_⟩
      have hnone : ((List.replicate s (clauseAddrs C ([] : CNF (Fin n)))).sections.any fun D =>
          !(D.map fun p => List.range' (p + 1) (y.mem p)).sections.any fun E =>
            compatCodes (fun v => y.mem (Tb + v)) x b.toNat (E.map y.mem)) = false := by
        rcases s with _ | s
        · simp [compatCodes]
        · rw [show clauseAddrs C ([] : CNF (Fin n)) = [] from rfl,
            sections_eq_nil_of_nil_mem (List.mem_replicate.mpr ⟨by omega, rfl⟩)]
          rfl
      wram_simp
      simp [addrTest, hfirst, hnone]
    · have hlt : C < C + (encodeClauses (c₀ :: φ')).length := by
        simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
      wram_exec [hf.b_eq, hf.cBeg_eq, hf.cEnd_eq]
      wram_call (outerSearch_spec (List.cons_ne_nil c₀ φ') _ (by imp_frame hf))
        with z ⟨hzf, hzm, hzs⟩
      refine ⟨by simp only [impScanTime, outerTime]; omega, hzf, hzm, ?_⟩
      rw [hzs]
      simp only [Data.set_mem, addrTest, hfirst, Bool.false_or]
      congr 1
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false]
      refine forall₂_congr fun D hD => ?_
      have hD' := (mem_sections_replicate.mp hD).2
      have hmap : (D.map fun p => List.range' (p + 1) (y.mem p)) =
          D.map (litAddrs C (c₀ :: φ')) :=
        List.map_congr_left fun p hp => by
          rw [litAddrs, mem_clauseAddr hf.clauses (hD' p hp)]
      rw [hmap, clauseOk, List.any_eq_true]
      simp only [litOk, not_forall, not_not, exists_prop]

end Scan

/-! ### The implied value -/

/-- Set `D` and `E` back to zero. -/
def zeroBody : Code .standard 32 := ram[ adr ← dBase + jR; *adr ← zero; jR ← jR + one ]

/-- Set the words `jR, …, 2 s - 1` after `dBase` to zero. -/
def zeroLoop : Code .standard 32 := .loop (.lt jR stop) zeroBody

/-- **Clear the scratch memory** of `D` and `E`. -/
def zeroScratch : Code .standard 32 := ram[ jR ← zero; stop ← sReg + sReg; ⟪zeroLoop⟫ ]

/-- Read the bound `s` from the word at `tBase + 2 n`, set the addresses of `D` and `E` just after
it, and start with the polarity `true`. -/
def impSetup : Code .standard 32 := ram[
  dBase ← tBase + nReg; dBase ← dBase + nReg; sReg ← *dBase; dBase ← dBase + one;
  eBase ← dBase + sReg; bReg ← one ]

/-- **The value w-implied on `xReg`**, stored in `res` as `optCode (implied φ s τ x)`. The bound
`s` is read from the word at `tBase + 2 n`, and the arrays `D` and `E` take the `2 s` words after
it, which are cleared at the end. -/
def impliedCode : Code .standard 32 := ram[
  ⟪impSetup⟫; ⟪impScan⟫;
  if sat = zero then [ res ← one ]
  else [ bReg ← zero; ⟪impScan⟫; if sat = zero then [ res ← zero ] else [ res ← two ] ];
  ⟪zeroScratch⟫ ]

/-- **The instruction bound of `impliedCode`** for the bound `s` and a clause encoding of length
`E`: two searches over at most `E ^ s` choices of clauses, each with at most `E ^ s` choices of
literals. -/
def impliedTime (s E : ℕ) : ℕ := 2 * impScanTime s E + 10 * s + 16

/-- **The instruction bound in closed form**: `impliedTime s E ≤ 140 (s + 1)² (E + 1)^(2 s)`. -/
theorem impliedTime_le (s E : ℕ) :
    impliedTime s E ≤ 140 * (s + 1) ^ 2 * (E + 1) ^ (2 * s) := by
  have hP : E ^ s ≤ (E + 1) ^ s := Nat.pow_le_pow_left (Nat.le_succ E) s
  have hF : 1 ≤ (E + 1) ^ s := Nat.one_le_pow _ _ (Nat.succ_pos E)
  rw [show 2 * s = s * 2 by ring, pow_mul]
  simp only [impliedTime, impScanTime, outerTime, outerIter, innerTime, innerIter, goodTime]
  generalize E ^ s = P at *
  generalize (E + 1) ^ s = F at *
  have hFF : 1 ≤ F * F := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hA : P * (48 * s + 32) ≤ F * F * (48 * s + 32) :=
    Nat.mul_le_mul_right _ (hP.trans (Nat.le_mul_self F))
  have hB : P * P * (18 * s ^ 2 + 72 * s + 26) ≤ F * F * (18 * s ^ 2 + 72 * s + 26) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hP hP)
  have hC : 20 * s + 40 ≤ F * F * (20 * s + 40) := Nat.le_mul_of_pos_left _ hFF
  have hD : F * F * (18 * s ^ 2 + 140 * s + 98) ≤ F * F * (140 * s ^ 2 + 280 * s + 140) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  calc 2 * (5 * s + 6 + P * (12 * s + 8 + P * (s * (9 * s + 22) + 4 + 14 * s + 9) + 12 * s + 8)
        + 6) + 10 * s + 16
      = 20 * s + 40 + P * (48 * s + 32) + P * P * (18 * s ^ 2 + 72 * s + 26) := by ring
    _ ≤ F * F * (20 * s + 40) + F * F * (48 * s + 32) + F * F * (18 * s ^ 2 + 72 * s + 26) := by
        omega
    _ = F * F * (18 * s ^ 2 + 140 * s + 98) := by ring
    _ ≤ F * F * (140 * s ^ 2 + 280 * s + 140) := hD
    _ = 140 * (s + 1) ^ 2 * F ^ 2 := by ring

section ImpliedCode

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The frame with another polarity. -/
theorem ImpFrame.setB {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) (b' : Bool) :
    ImpFrame w φ τ x b' C Tb s Db (y.set bReg b'.toNat) :=
  { h with
    zero_eq := by wram_simp [h.zero_eq]
    one_eq := by wram_simp [h.one_eq]
    x_eq := by wram_simp [h.x_eq]
    b_eq := by wram_simp
    cBeg_eq := by wram_simp [h.cBeg_eq]
    cEnd_eq := by wram_simp [h.cEnd_eq]
    tBase_eq := by wram_simp [h.tBase_eq]
    s_eq := by wram_simp [h.s_eq]
    dBase_eq := by wram_simp [h.dBase_eq]
    eBase_eq := by wram_simp [h.eBase_eq] }

/-- **The clearing loop** from word `j`: the words `j, …, 2 s - 1` after `Db` become zero, and
the other memory is unchanged. -/
private theorem zeroLoop_spec : ∀ (d : ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs stop = 2 * s → y.regs jR + d = 2 * s →
    ∃ z, ExecWithin w zeroLoop y z (5 * d + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ i, y.regs jR ≤ i → i < 2 * s → z.mem (Db + i) = 0) ∧
      ∀ a, a < Db + y.regs jR ∨ Db + 2 * s ≤ a → z.mem a = y.mem a := by
  intro d y hf hst hd
  obtain ⟨z, hz, hzf, hzl, hzm⟩ :=
    fillDLoop_spec ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ le_rfl (fits_zero w)
      d y hf hst hf.zero_eq hd
  refine ⟨z, hz, hzf, fun i h1 h2 => ?_, hzm⟩
  have hget := hzl.get (i - y.regs jR) (by simp; omega)
  simpa [show Db + y.regs jR + (i - y.regs jR) = Db + i by omega] using hget

/-- **Clear the scratch memory**: the `2 s` words of `D` and `E` become zero, and the other memory
is unchanged, within `10 s + 4` instructions. -/
private theorem zeroScratch_spec (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w zeroScratch y z (10 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ i < 2 * s, z.mem (Db + i) = 0) ∧ ∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a := by
  unfold zeroScratch
  wram_exec [hf.fits_le, hf.zero_eq, hf.s_eq]
  wram_call (zeroLoop_spec (2 * s) _ (by imp_frame hf) (by wram_simp; omega) (by wram_simp))
    with z ⟨hzf, hz0, hzm⟩
  wram_simp at hz0 hzm
  exact ⟨by omega, hzf, fun i hi => hz0 i (Nat.zero_le _) hi,
    fun a ha => hzm a (by simpa using ha)⟩

/-- **The value w-implied on `x`.** From the clauses of `φ` stored in `[cBeg, cEnd)` below the
partial assignment `τ` stored at `tBase = Tb`, the bound `s` stored at `Tb + 2 n` and `2 s` zero
words after it, `impliedCode` stores `optCode (implied φ s τ x)` in `res` within
`impliedTime s E` instructions, where `E` is the length of the encoding of the clauses, and leaves
memory unchanged. -/
theorem impliedCode_spec (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (s : ℕ)
    {C Tb : ℕ} (y : Data 32) (hz : y.regs zero = 0) (ho : y.regs one = 1)
    (htwo : y.regs two = 2) (hx : y.regs xReg = x) (hC : y.regs cBeg = C)
    (hCe : y.regs cEnd = C + (encodeClauses φ).length) (hTb : y.regs tBase = Tb)
    (hn : y.regs nReg = n) (hcl : HoldsList C (encodeClauses φ) y.mem)
    (hτ : PartialAt y.mem Tb τ) (hle : C + (encodeClauses φ).length ≤ Tb)
    (hs : y.mem (Tb + 2 * n) = s) (hzero : ∀ i < 2 * s, y.mem (Tb + 2 * n + 1 + i) = 0)
    (hw : Fits w (Tb + 2 * n + 2 * s + 2)) :
    ∃ z, ExecWithin w impliedCode y z (impliedTime s (encodeClauses φ).length) ∧
      z.mem = y.mem ∧ z.regs res = optCode (implied φ s τ x) := by
  set Db := Tb + 2 * n + 1 with hDb
  have hs' : y.mem (Tb + n + n) = s := by rw [← hs]; congr 1; omega
  have hfit_all (v : ℕ) (hv : v ≤ Tb + 2 * n + 2 * s + 2) : Fits w v := hw.of_le hv
  have finish {b₀ : Bool} {u : Data 32} {Q : Data 32 → ℕ → Prop}
      (huf : ImpFrame w φ τ x b₀ C Tb s Db u)
      (hum : ∀ a, a < Db ∨ Db + 2 * s ≤ a → u.mem a = y.mem a)
      (hQ : ∀ z, z.mem = y.mem → z.regs res = u.regs res → Q z (10 * s + 4)) :
      WP w zeroScratch u Q := by
    obtain ⟨z', hz', -, hz'0, hz'm⟩ := zeroScratch_spec u huf
    refine WP.of_execWithin hz' (hQ z' ?_ (hz'.regs_eq (by decide)))
    funext a
    by_cases ha : a < Db ∨ Db + 2 * s ≤ a
    · exact (hz'm a ha).trans (hum a ha)
    · obtain ⟨i, hi, rfl⟩ : ∃ i < 2 * s, a = Db + i := ⟨a - Db, by omega, by omega⟩
      exact (hz'0 i hi).trans (hzero i hi).symm
  rw [implied_eq_test]
  unfold impliedCode impSetup
  wram_exec [hfit_all, hTb, hn, hs', ho]
  refine WP.name fun y₁ hy₁_eq => ?_
  have hy₁ : ImpFrame w φ τ x true C Tb s Db y₁ :=
    { zero_eq := by subst hy₁_eq; wram_simp [hz]
      one_eq := by subst hy₁_eq; wram_simp [ho]
      x_eq := by subst hy₁_eq; wram_simp [hx]
      b_eq := by subst hy₁_eq; wram_simp; rfl
      cBeg_eq := by subst hy₁_eq; wram_simp [hC]
      cEnd_eq := by subst hy₁_eq; wram_simp [hCe]
      tBase_eq := by subst hy₁_eq; wram_simp [hTb]
      s_eq := by subst hy₁_eq; wram_simp
      dBase_eq := by subst hy₁_eq; wram_simp [hDb]; omega
      eBase_eq := by subst hy₁_eq; wram_simp [hDb]; omega
      clauses := hy₁_eq ▸ hcl
      stored := hy₁_eq ▸ hτ
      clauses_le := by omega
      stored_le := by omega
      codes_le := by omega
      fits := hw.of_le (by omega) }
  have hy₁_two : y₁.regs two = 2 := by subst hy₁_eq; wram_simp [htwo]
  have hy₁_mem : y₁.mem = y.mem := by subst hy₁_eq; rfl
  obtain ⟨z₁, hz₁, hz₁f, hz₁m, hz₁s⟩ := impScan_spec y₁ hy₁
  have hz₁m' : ∀ a, a < Db ∨ Db + 2 * s ≤ a → z₁.mem a = y.mem a :=
    fun a ha => (hz₁m a ha).trans (congrFun hy₁_mem a)
  refine WP.of_execWithin hz₁ ?_
  rcases ht : impliedTest φ s τ x true
  · wram_exec [hz₁s, ht, hz₁f.zero_eq]
    obtain ⟨z₂, hz₂, hz₂f, hz₂m, hz₂s⟩ := impScan_spec (z₁.set bReg 0) (hz₁f.setB false)
    have hz₂m' : ∀ a, a < Db ∨ Db + 2 * s ≤ a → z₂.mem a = y.mem a :=
      fun a ha => (hz₂m a ha).trans (hz₁m' a ha)
    refine WP.of_execWithin hz₂ ?_
    rcases hf' : impliedTest φ s τ x false
    · have htwo₂ : z₂.regs two = 2 := (hz₂.regs_eq (by decide)).trans
        ((by wram_simp : (z₁.set bReg 0).regs two = z₁.regs two).trans
          ((hz₁.regs_eq (by decide)).trans hy₁_two))
      wram_exec [hz₂s, hf', hz₂f.zero_eq, htwo₂]
      refine finish (by imp_frame hz₂f) (fun a ha => hz₂m' a ha) fun z hzm hzr =>
        ⟨by simp only [impliedTime]; omega, hzm, hzr.trans (by wram_simp; simp [optCode])⟩
    · wram_exec [hz₂s, hf', hz₂f.zero_eq]
      refine finish (by imp_frame hz₂f) (fun a ha => hz₂m' a ha) fun z hzm hzr =>
        ⟨by simp only [impliedTime]; omega, hzm, hzr.trans (by wram_simp; simp [optCode])⟩
  · wram_exec [hz₁s, ht, hz₁f.zero_eq, hz₁f.one_eq]
    refine finish (by imp_frame hz₁f) (fun a ha => hz₁m' a ha) fun z hzm hzr =>
      ⟨by simp only [impliedTime]; omega, hzm, hzr.trans (by wram_simp; simp [optCode])⟩

end ImpliedCode

end Cslib.Algorithms.WordRAM.PPSZ
