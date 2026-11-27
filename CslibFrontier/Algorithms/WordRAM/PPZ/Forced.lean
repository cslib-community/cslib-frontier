/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.Schoening.Scan
public import CslibFrontier.Computability.Complexity.FineGrained.PPZ

/-!
# Forced values of PPZ on the word RAM

A partial assignment `τ : Fin n → Option Bool` is stored as `n` words, `0` or `1` for a set
variable and `2` for an unset one (`Cslib.Algorithms.WordRAM.PPZ.PartialAt`). The formula is
stored as in `Cslib.Algorithms.WordRAM.Schoening.encodeClauses`: each clause is its length followed
by the codes `2 v + b` of its literals.

`Cslib.Algorithms.WordRAM.PPZ.unitScan` scans the clauses once and reports whether one of them is a
unit clause on the variable `x` with polarity `b` under `τ` (`Cslib.Complexity.PPZ.IsUnitOn`): a
clause that contains `(x, b)`, whose literals on `x` all have polarity `b`, and whose other literals
`τ` falsifies. `Cslib.Algorithms.WordRAM.PPZ.forcedCode` runs it for the polarity `true` and then,
if needed, for `false`, and stores the word of `Cslib.Complexity.PPZ.forced φ τ x`
(`Cslib.Algorithms.WordRAM.PPZ.forcedCode_spec`). Both leave memory unchanged and take
`O(E)` instructions, where `E` is the length of the encoding of the clauses.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPZ.optCode`, `Cslib.Algorithms.WordRAM.PPZ.PartialAt`: storing a
  partial assignment.
* `Cslib.Algorithms.WordRAM.PPZ.litHas`, `Cslib.Algorithms.WordRAM.PPZ.litOk`: the two literal
  tests of a unit clause.
* `Cslib.Algorithms.WordRAM.PPZ.unitScan`, `Cslib.Algorithms.WordRAM.PPZ.forcedCode`: the scans.

## Main results

* `Cslib.Algorithms.WordRAM.PPZ.isUnitOn_iff`: a unit clause through its literal tests.
* `Cslib.Algorithms.WordRAM.PPZ.unitScan_spec`: the scan finds a unit clause exactly when there is
  one.
* `Cslib.Algorithms.WordRAM.PPZ.forcedCode_spec`: the forced value, within `28 E + 15`
  instructions.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPZ
open Cslib.Algorithms.WordRAM.Schoening (litCode encodeClause encodeClause_eq encodeClauses
  litCode_shiftRight litCode_and_one length_encodeClause encodeClauses_cons encodeClauses_nil
  litCode_lt one_sub_toNat_xor toNat_or toNat_xor_le_one)

variable {n : ℕ}

/-! ### Partial assignments -/

/-- The word of a value of a partial assignment: `0` or `1` when set, `2` when unset. -/
def optCode : Option Bool → ℕ
  | some b => b.toNat
  | none => 2

theorem optCode_le_two (o : Option Bool) : optCode o ≤ 2 := by
  rcases o with _ | b
  · exact le_rfl
  · cases b <;> decide

/-- The partial assignment `τ` is stored as the words `optCode (τ i)` from address `base`. -/
def PartialAt (mem : ℕ → ℕ) (base : ℕ) (τ : Fin n → Option Bool) : Prop :=
  ∀ i : Fin n, mem (base + i) = optCode (τ i)

/-! ### Unit clauses through literal tests -/

/-- Whether the literal `l` is `(x, b)`. -/
def litHas (x : Fin n) (b : Bool) (l : Literal (Fin n)) : Bool := l.1 == x && l.2 == b

/-- Whether the literal `l` may occur in a unit clause on `x` with polarity `b` under `τ`: a literal
on `x` must have polarity `b`, and `τ` must falsify any other literal. -/
def litOk (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (l : Literal (Fin n)) : Bool :=
  if l.1 = x then l.2 == b else τ l.1 == some (!l.2)

/-- A unit clause through its literal tests. -/
theorem isUnitOn_iff (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (c : Clause (Fin n)) :
    IsUnitOn τ x b c ↔ c.any (litHas x b) = true ∧ c.all (litOk τ x b) = true := by
  simp only [IsUnitOn, List.any_eq_true, List.all_eq_true, litHas, litOk, Bool.and_eq_true,
    beq_iff_eq]
  refine and_congr Iff.rfl (forall₂_congr fun l _ => ?_)
  split_ifs <;> simp

/-- Whether the clause `c` is a unit clause on `x` with polarity `b` under `τ`, through the literal
tests. -/
def unitTest (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (c : Clause (Fin n)) : Bool :=
  c.any (litHas x b) && c.all (litOk τ x b)

/-- The value forced by unit clauses, through the literal tests. -/
theorem forced_eq_ite (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) :
    forced φ τ x =
      if φ.any (unitTest τ x true) then some true
      else if φ.any (unitTest τ x false) then some false
      else none := by
  have key (b : Bool) : (∃ c ∈ φ, IsUnitOn τ x b c) ↔ φ.any (unitTest τ x b) = true := by
    simp only [isUnitOn_iff, unitTest, List.any_eq_true, Bool.and_eq_true]
  unfold forced
  simp only [key]

private theorem toNat_and (a b : Bool) : a.toNat &&& b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

/-- The partial-assignment test of `litOk`: `τ v` is `some (!s)` exactly when its word is
`1 - s`. -/
theorem optCode_eq_one_sub_iff (o : Option Bool) (s : Bool) :
    optCode o = 1 - s.toNat ↔ o = some (!s) := by
  rcases o with _ | a
  · cases s <;> simp [optCode]
  · cases a <;> cases s <;> simp [optCode]

/-! ### Registers -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 32 := 0
/-- Constant `1`. -/
abbrev one : Fin 32 := 1
/-- Address of the first clause. -/
abbrev cBeg : Fin 32 := 2
/-- End address of the clauses. -/
abbrev cEnd : Fin 32 := 3
/-- Address of the stored partial assignment. -/
abbrev tBase : Fin 32 := 4
/-- The number `n` of variables. -/
abbrev nReg : Fin 32 := 5
/-- Address of the current clause. -/
abbrev ptr : Fin 32 := 6
/-- Length of the current clause. -/
abbrev len : Fin 32 := 7
/-- Address of the current literal. -/
abbrev lptr : Fin 32 := 8
/-- End address of the current clause. -/
abbrev lend : Fin 32 := 9
/-- The current literal code. -/
abbrev lit : Fin 32 := 10
/-- The current variable. -/
abbrev var : Fin 32 := 11
/-- The sign of the current literal. -/
abbrev sgn : Fin 32 := 12
/-- Scratch address. -/
abbrev addr : Fin 32 := 13
/-- Scratch value. -/
abbrev val : Fin 32 := 14
/-- Scratch comparison. -/
abbrev eq : Fin 32 := 15
/-- Whether the current clause contains `(x, b)`. -/
abbrev hasLit : Fin 32 := 16
/-- Whether every literal of the current clause passes `litOk`. -/
abbrev ok : Fin 32 := 17
/-- Whether a unit clause was found. -/
abbrev fnd : Fin 32 := 18
/-- The variable `x`. -/
abbrev xReg : Fin 32 := 19
/-- The polarity `b`. -/
abbrev bReg : Fin 32 := 20
/-- The word of the forced value. -/
abbrev res : Fin 32 := 21
/-- Constant `2`. -/
abbrev two : Fin 32 := 22

end Reg

open Reg

/-! ### The scan -/

/-- One literal: read it, and update `hasLit` and `ok`. -/
def litBody : Code .standard 32 := ram[
  lit ← *lptr; var ← lit >>> one; sgn ← lit &&& one;
  if var = xReg then [ eq ← sgn ^^^ bReg; eq ← one - eq; hasLit ← hasLit ||| eq; ok ← ok &&& eq ]
  else [ addr ← tBase + var; val ← *addr; eq ← one - sgn;
    if val = eq then [ ok ← ok ] else [ ok ← zero ] ];
  lptr ← lptr + one ]

/-- Test the literals in `[lptr, lend)`. -/
def litLoop : Code .standard 32 := .loop (.lt lptr lend) litBody

/-- Read the length of the clause at `ptr` and set up its literal loop. -/
def clauseInit : Code .standard 32 := ram[
  len ← *ptr; lptr ← ptr + one; lend ← lptr + len; hasLit ← zero; ok ← one ]

/-- After a clause: record whether it is a unit clause and move on. -/
def clauseDone : Code .standard 32 := ram[ eq ← hasLit &&& ok; fnd ← fnd ||| eq; ptr ← lend ]

/-- One clause. -/
def clauseBody : Code .standard 32 := ram[ ⟪clauseInit⟫; ⟪litLoop⟫; ⟪clauseDone⟫ ]

/-- Test the clauses in `[ptr, cEnd)`. -/
def clauseLoop : Code .standard 32 := .loop (.lt ptr cEnd) clauseBody

/-- **The unit-clause scan**: whether some clause is a unit clause on `xReg` with polarity
`bReg`. -/
def unitScan : Code .standard 32 := ram[ ptr ← cBeg; fnd ← zero; ⟪clauseLoop⟫ ]

/-- **The forced value** of `xReg`, stored in `res` as `optCode (forced φ τ x)`. -/
def forcedCode : Code .standard 32 := ram[
  bReg ← one; ⟪unitScan⟫;
  if fnd = one then [ res ← one ]
  else [ bReg ← zero; ⟪unitScan⟫; if fnd = one then [ res ← zero ] else [ res ← two ] ] ]

section Specs

variable {w : ℕ}

/-- The registers the scan relies on. -/
structure ScanFrame (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) (y : Data 32) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  two_eq : y.regs two = 2
  x_eq : y.regs xReg = x
  stored : PartialAt y.mem (y.regs tBase) τ
  fits : Fits w (y.regs tBase + 2 * n)
  pos : 1 ≤ y.regs tBase

/-- **One literal.** -/
theorem litBody_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (l : Literal (Fin n))
    (h o : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hl : y.mem (y.regs lptr) = litCode l) (hh : y.regs hasLit = h.toNat)
    (ho : y.regs ok = o.toNat) (hlp : Fits w (y.regs lptr + 1)) :
    ∃ z, ExecWithin w litBody y z 12 ∧ z.mem = y.mem ∧
      z.regs hasLit = (h || litHas x b l).toNat ∧ z.regs ok = (o && litOk τ x b l).toNat ∧
      z.regs lptr = y.regs lptr + 1 := by
  have : Fits w l.1.val := hf.fits.of_le (by omega)
  have : Fits w l.2.toNat := hf.fits.of_le (by have := Bool.toNat_le l.2; have := hf.pos; omega)
  refine WP.exists_execWithin ?_
  unfold litBody
  by_cases hvx : l.1 = x
  · subst hvx
    have : Fits w (l.2.toNat ^^^ b.toNat) :=
      hf.fits.of_le (by have := toNat_xor_le_one l.2 b; have := hf.pos; omega)
    have : Fits w (1 - (l.2.toNat ^^^ b.toNat)) := hf.fits.of_le (by have := hf.pos; omega)
    have : Fits w (h.toNat ||| (1 - (l.2.toNat ^^^ b.toNat))) := hf.fits.of_le (by
      rw [one_sub_toNat_xor, toNat_or]; have := Bool.toNat_le (h || (l.2 == b)); have := hf.pos
      omega)
    have : Fits w (o.toNat &&& (1 - (l.2.toNat ^^^ b.toNat))) := hf.fits.of_le (by
      rw [one_sub_toNat_xor, toNat_and]; have := Bool.toNat_le (o && (l.2 == b)); have := hf.pos
      omega)
    wram_exec [hl, hf.one_eq, litCode_shiftRight, litCode_and_one, hf.x_eq, hb, hh, ho]
    exact ⟨rfl, by wram_simp; simp +decide [one_sub_toNat_xor, toNat_or, litHas],
      by wram_simp; simp +decide [one_sub_toNat_xor, toNat_and, litOk], by wram_simp⟩
  · have hvx' : l.1.val ≠ x.val := fun h' => hvx (Fin.ext h')
    have hbx : (l.1 == x) = false := beq_eq_false_iff_ne.mpr hvx
    have : Fits w (y.regs tBase + l.1.val) := hf.fits.of_le (by omega)
    have : Fits w (1 - l.2.toNat) := hf.fits.of_le (by have := hf.pos; omega)
    by_cases hve : optCode (τ l.1) = 1 - l.2.toNat <;>
      wram_exec [hl, hf.one_eq, hf.zero_eq, litCode_shiftRight, litCode_and_one, hf.x_eq, hvx',
        hf.stored l.1, hve, ho]
    · exact ⟨rfl, by wram_simp [hh]; simp +decide [litHas, hbx],
        by wram_simp [ho]; simp +decide [litOk, hvx, (optCode_eq_one_sub_iff _ _).mp hve],
        by wram_simp⟩
    · have hτf : (τ l.1 == some (!l.2)) = false :=
        beq_eq_false_iff_ne.mpr fun h' => hve ((optCode_eq_one_sub_iff _ _).mpr h')
      exact ⟨rfl, by wram_simp [hh]; simp +decide [litHas, hbx],
        by wram_simp [hf.zero_eq]; simp +decide [litOk, hvx, hτf], by wram_simp⟩

/-- Code that writes none of the registers of `ScanFrame`. -/
def PreservesScan (c : Code .standard 32) : Prop :=
  c.Preserves zero ∧ c.Preserves one ∧ c.Preserves two ∧ c.Preserves xReg ∧ c.Preserves tBase

instance (c : Code .standard 32) : Decidable (PreservesScan c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A run of code that keeps the scan registers and memory keeps the scan frame. -/
theorem ScanFrame.of_exec {τ : Fin n → Option Bool} {x : Fin n} {c : Code .standard 32}
    {y z : Data 32} {T : ℕ} (hf : ScanFrame w τ x y) (hc : PreservesScan c)
    (he : ExecWithin w c y z T) (hm : z.mem = y.mem) : ScanFrame w τ x z where
  zero_eq := (he.regs_eq hc.1).trans hf.zero_eq
  one_eq := (he.regs_eq hc.2.1).trans hf.one_eq
  two_eq := (he.regs_eq hc.2.2.1).trans hf.two_eq
  x_eq := (he.regs_eq hc.2.2.2.1).trans hf.x_eq
  stored := by rw [hm, he.regs_eq hc.2.2.2.2]; exact hf.stored
  fits := by rw [he.regs_eq hc.2.2.2.2]; exact hf.fits
  pos := by rw [he.regs_eq hc.2.2.2.2]; exact hf.pos

/-- The scan frame after setting a register outside it. -/
theorem ScanFrame.set {τ : Fin n → Option Bool} {x : Fin n} {y : Data 32} (hf : ScanFrame w τ x y)
    {i : Fin 32} (hi : i ≠ zero ∧ i ≠ one ∧ i ≠ two ∧ i ≠ xReg ∧ i ≠ tBase) (v : ℕ) :
    ScanFrame w τ x (y.set i v) where
  zero_eq := by wram_simp [hi.1.symm, hf.zero_eq]
  one_eq := by wram_simp [hi.2.1.symm, hf.one_eq]
  two_eq := by wram_simp [hi.2.2.1.symm, hf.two_eq]
  x_eq := by wram_simp [hi.2.2.2.1.symm, hf.x_eq]
  stored := by simpa [Function.update_of_ne hi.2.2.2.2.symm] using hf.stored
  fits := by simpa [Function.update_of_ne hi.2.2.2.2.symm] using hf.fits
  pos := by simpa [Function.update_of_ne hi.2.2.2.2.symm] using hf.pos

/-- **The literal loop.** From `hasLit = h` and `ok = o`, the loop over the literals `ls` ends with
`hasLit = h || ls.any (litHas x b)` and `ok = o && ls.all (litOk τ x b)`, and unchanged memory. -/
theorem litLoop_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (ls : Clause (Fin n))
    (h o : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hl : HoldsList (y.regs lptr) (ls.map litCode) y.mem)
    (hend : y.regs lend = y.regs lptr + ls.length) (hh : y.regs hasLit = h.toNat)
    (ho : y.regs ok = o.toNat) (hle : Fits w (y.regs lend)) :
    ∃ z, ExecWithin w litLoop y z (14 * ls.length + 2) ∧ z.mem = y.mem ∧
      z.regs hasLit = (h || ls.any (litHas x b)).toNat ∧
      z.regs ok = (o && ls.all (litOk τ x b)).toNat ∧ z.regs lptr = y.regs lend ∧
      ScanFrame w τ x z ∧ z.regs bReg = b.toNat ∧ z.regs lend = y.regs lend := by
  induction ls generalizing y h o with
  | nil =>
    refine ⟨y, (ExecWithin.loop_exit ?_).mono (by omega), rfl, by simpa using hh,
      by simpa using ho, by simp [hend], hf, hb, rfl⟩
    simp [Cond.holds_lt, hend]
  | cons l ls ih =>
    have hc : (Cond.lt lptr lend).Holds y := by
      simp only [Cond.holds_lt, hend, List.length_cons]; omega
    have hlit : y.mem (y.regs lptr) = litCode l := by
      simpa using hl.get 0 (by simp)
    have hrest : HoldsList (y.regs lptr + 1) (ls.map litCode) y.mem := by
      have := (holdsList_append_iff (xs := [litCode l]) (ys := ls.map litCode)).mp
        (by simpa using hl)
      simpa using this.2
    obtain ⟨z₁, he₁, hm₁, hh₁, ho₁, hp₁⟩ := litBody_spec τ x b l h o y hf hb hlit hh ho
      (hle.of_le (by simp only [List.length_cons] at hend; omega))
    have hf₁ := hf.of_exec (by decide) he₁ hm₁
    have hb₁ : z₁.regs bReg = b.toNat := by rw [he₁.regs_eq (by decide)]; exact hb
    have hlend₁ : z₁.regs lend = y.regs lend := he₁.regs_eq (by decide)
    obtain ⟨z, he, hm, hhz, hoz, hpz, hfz, hbz, hlz⟩ := ih (h || litHas x b l)
      (o && litOk τ x b l) z₁ hf₁ hb₁ (by rw [hp₁, hm₁]; exact hrest)
      (by rw [hlend₁, hp₁, hend, List.length_cons]; omega) hh₁ ho₁ (by rw [hlend₁]; exact hle)
    refine ⟨z, (ExecWithin.loop_iter hc he₁ he).mono (by simp only [List.length_cons]; omega),
      hm.trans hm₁, ?_, ?_, by rw [hpz, hlend₁], hfz, hbz, hlz.trans hlend₁⟩
    · rw [hhz, List.any_cons, Bool.or_assoc]
    · rw [hoz, List.all_cons, Bool.and_assoc]

/-- Preserving the registers of `ScanFrame` and memory preserves `ScanFrame`. -/
private theorem ScanFrame.of_regs {τ : Fin n → Option Bool} {x : Fin n} {y z : Data 32}
    (hf : ScanFrame w τ x y) (hz : z.regs zero = y.regs zero) (ho : z.regs one = y.regs one)
    (ht : z.regs two = y.regs two) (hx : z.regs xReg = y.regs xReg)
    (hb : z.regs tBase = y.regs tBase) (hm : z.mem = y.mem) : ScanFrame w τ x z where
  zero_eq := hz.trans hf.zero_eq
  one_eq := ho.trans hf.one_eq
  two_eq := ht.trans hf.two_eq
  x_eq := hx.trans hf.x_eq
  stored := by rw [hm, hb]; exact hf.stored
  fits := by rw [hb]; exact hf.fits
  pos := by rw [hb]; exact hf.pos

/-- **The clause loop.** From `ptr` at the encoding of the clauses `ψ`, which end at `cEnd`, and
`fnd = f`, the loop ends with `fnd = f || ψ.any (unitTest τ x b)` and unchanged memory. -/
theorem clauseLoop_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (ψ : CNF (Fin n))
    (f : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hp : HoldsList (y.regs ptr) (encodeClauses ψ) y.mem)
    (hend : y.regs ptr + (encodeClauses ψ).length = y.regs cEnd) (hfnd : y.regs fnd = f.toNat)
    (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w clauseLoop y z (14 * (encodeClauses ψ).length + 2) ∧ z.mem = y.mem ∧
      z.regs fnd = (f || ψ.any (unitTest τ x b)).toNat ∧ ScanFrame w τ x z ∧
      z.regs bReg = b.toNat ∧ z.regs cEnd = y.regs cEnd ∧ z.regs cBeg = y.regs cBeg := by
  induction ψ generalizing y f with
  | nil =>
    refine ⟨y, (ExecWithin.loop_exit ?_).mono le_rfl, rfl, by simpa using hfnd, hf, hb, rfl, rfl⟩
    simp only [encodeClauses_nil, List.length_nil, Nat.add_zero] at hend
    simp [Cond.holds_lt, hend]
  | cons c ψ ih =>
    rw [encodeClauses_cons] at hp hend ⊢
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hp
    simp only [List.length_append, length_encodeClause] at hend hpψ ⊢
    have hlen : y.mem (y.regs ptr) = c.length := by
      simpa [encodeClause_eq] using hpc.get 0 (by simp)
    have hlits : HoldsList (y.regs ptr + 1) (c.map litCode) y.mem :=
      ((holdsList_append_iff (xs := [c.length]) (ys := c.map litCode)).mp
        (by simpa [encodeClause_eq] using hpc)).2
    have hf2 : Fits w (y.regs ptr + 1 + c.length) := hce.of_le (by omega)
    have hu : Fits w ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat) :=
      hf.fits.of_le (by rw [toNat_and]; have := Bool.toNat_le (c.any (litHas x b) &&
        c.all (litOk τ x b)); have := hf.pos; omega)
    have hu' : Fits w (f.toNat ||| ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat)) :=
      hf.fits.of_le (by rw [toNat_and, toNat_or]; have := Bool.toNat_le (f ||
        (c.any (litHas x b) && c.all (litOk τ x b))); have := hf.pos; omega)
    refine WP.exists_execWithin (WP.loop_iter (by simp only [Cond.holds_lt]; omega) ?_)
    unfold clauseBody clauseInit clauseDone
    wram_exec [hlen, hf.one_eq, hf.zero_eq]
    refine WP.name fun y₁ hy₁ => ?_
    obtain ⟨z₂, he₂, hm₂, hh₂, ho₂, hp₂, hf₂, hb₂, hl₂⟩ := litLoop_spec τ x b c false true y₁
      (hf.of_regs (by wram_simp [hy₁]) (by wram_simp [hy₁]) (by wram_simp [hy₁])
        (by wram_simp [hy₁]) (by wram_simp [hy₁]) (by simp [hy₁]))
      (by wram_simp [hy₁, hb]) (by wram_simp [hy₁]; exact hlits)
      (by wram_simp [hy₁, List.length_map]) (by wram_simp [hy₁]; rfl)
      (by wram_simp [hy₁]; rfl) (by wram_simp [hy₁]; exact hf2)
    simp only [Bool.false_or, Bool.true_and] at hh₂ ho₂
    have hfnd₂ : z₂.regs fnd = f.toNat :=
      (he₂.regs_eq (by decide)).trans (by wram_simp [hy₁, hfnd])
    have hcEnd₂ : z₂.regs cEnd = y.regs cEnd :=
      (he₂.regs_eq (by decide)).trans (by wram_simp [hy₁])
    have hcBeg₂ : z₂.regs cBeg = y.regs cBeg :=
      (he₂.regs_eq (by decide)).trans (by wram_simp [hy₁])
    have hl₂' : z₂.regs lend = y.regs ptr + 1 + c.length := hl₂.trans (by wram_simp [hy₁])
    replace hm₂ : z₂.mem = y.mem := hm₂.trans (by simp [hy₁])
    refine WP.of_execWithin he₂ ?_
    wram_exec [hh₂, ho₂, hfnd₂, hl₂']
    wram_call (ih (f || unitTest τ x b c) _
      (hf₂.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) rfl)
      (by wram_simp [hb₂])
      (by simpa only [Data.set_regs, Function.update_self, Data.set_mem, hm₂,
        show y.regs ptr + 1 + c.length = y.regs ptr + (c.length + 1) by omega] using hpψ)
      (by wram_simp [hcEnd₂]; omega)
      (by wram_simp; simp [unitTest, toNat_and, toNat_or])
      (by wram_simp [hcEnd₂]; exact hce))
      with z ⟨hm, hfz, hfrz, hbz, hcz, hcbz⟩
    exact ⟨by omega, by wram_simp [hm, hm₂], by rw [hfz, List.any_cons, Bool.or_assoc], hfrz, hbz,
      by wram_simp [hcz, hcEnd₂], by wram_simp [hcbz, hcBeg₂]⟩

/-- **The unit-clause scan.** From the clauses of `φ` stored in `[cBeg, cEnd)`, the scan reports
whether `φ` has a unit clause on `x` with polarity `b` under `τ`, within `14 E + 4` instructions,
where `E` is the length of the encoding, and leaves memory unchanged. -/
theorem unitScan_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (φ : CNF (Fin n))
    (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hcl : HoldsList (y.regs cBeg) (encodeClauses φ) y.mem)
    (hend : y.regs cBeg + (encodeClauses φ).length = y.regs cEnd) (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w unitScan y z (14 * (encodeClauses φ).length + 4) ∧ z.mem = y.mem ∧
      z.regs fnd = (φ.any (unitTest τ x b)).toNat ∧ ScanFrame w τ x z ∧
      z.regs bReg = b.toNat ∧ z.regs cEnd = y.regs cEnd ∧ z.regs cBeg = y.regs cBeg := by
  refine WP.exists_execWithin ?_
  unfold unitScan
  wram_exec [hf.zero_eq]
  wram_call (clauseLoop_spec τ x b φ false _
    (hf.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) rfl)
    (by wram_simp [hb]) (by wram_simp; exact hcl) (by wram_simp [hend]) (by wram_simp; rfl)
    (by wram_simp; exact hce))
    with z ⟨hm, hfz, hfr, hbz, hcz, hcbz⟩
  exact ⟨by omega, by wram_simp [hm], by simpa using hfz, hfr, hbz, by wram_simp [hcz],
    by wram_simp [hcbz]⟩

/-- **The forced value.** From the clauses of `φ` stored in `[cBeg, cEnd)` and the partial
assignment `τ` stored at `tBase`, `forcedCode` stores `optCode (forced φ τ x)` in `res` within
`28 E + 15` instructions, where `E` is the length of the encoding, and leaves memory unchanged. -/
theorem forcedCode_spec (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (y : Data 32)
    (hf : ScanFrame w τ x y) (hcl : HoldsList (y.regs cBeg) (encodeClauses φ) y.mem)
    (hend : y.regs cBeg + (encodeClauses φ).length = y.regs cEnd) (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w forcedCode y z (28 * (encodeClauses φ).length + 15) ∧ z.mem = y.mem ∧
      z.regs res = optCode (forced φ τ x) ∧ ScanFrame w τ x z ∧ z.regs cEnd = y.regs cEnd ∧
      z.regs cBeg = y.regs cBeg := by
  rw [forced_eq_ite]
  refine WP.exists_execWithin ?_
  unfold forcedCode
  wram_exec [hf.one_eq]
  wram_call (unitScan_spec τ x true φ _
    (hf.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) rfl)
    (by wram_simp; rfl) (by exact hcl) (by wram_simp [hend]) (by wram_simp; exact hce))
    with z₁ ⟨hm₁, hfnd₁, hf₁, -, hce₁, hcb₁⟩
  by_cases ht : φ.any (unitTest τ x true) = true
  · wram_exec [hfnd₁, ht, hf₁.one_eq]
    exact ⟨by wram_simp [hm₁], by wram_simp; simp [ht, optCode],
      hf₁.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) rfl,
      by wram_simp [hce₁], by wram_simp [hcb₁]⟩
  · wram_exec [hfnd₁, ht, hf₁.one_eq, hf₁.zero_eq]
    wram_call (unitScan_spec τ x false φ _
      (hf₁.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) rfl)
      (by wram_simp; rfl)
      (by wram_simp [hm₁, hcb₁]; exact hcl) (by wram_simp [hce₁, hcb₁, hend])
      (by wram_simp [hce₁]; exact hce))
      with z₂ ⟨hm₂, hfnd₂, hf₂, -, hce₂, hcb₂⟩
    simp only [ht, Bool.false_eq_true, ↓reduceIte]
    by_cases hf' : φ.any (unitTest τ x false) = true <;>
      wram_exec [hfnd₂, hf', hf₂.one_eq, hf₂.zero_eq, hf₂.two_eq] <;>
      exact ⟨by wram_simp [hm₂, hm₁], by wram_simp; simp [hf', optCode],
        hf₂.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) rfl,
        by wram_simp [hce₂, hce₁], by wram_simp [hcb₂, hcb₁]⟩

end Specs

end Cslib.Algorithms.WordRAM.PPZ
