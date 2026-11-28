/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop
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

theorem optCode_le_two (o : Option Bool) : optCode o ≤ 2 := by rcases o with _ | _ | _ <;> decide

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
  simp only [forced, key]

private theorem toNat_and (a b : Bool) : a.toNat &&& b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

/-- The partial-assignment test of `litOk`: `τ v` is `some (!s)` exactly when its word is
`1 - s`. -/
theorem optCode_eq_one_sub_iff (o : Option Bool) (s : Bool) :
    optCode o = 1 - s.toNat ↔ o = some (!s) := by
  rcases o with _ | _ | _ <;> cases s <;> decide

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

/-- The registers the scan relies on. The scan writes none of them and leaves memory unchanged, so
a call of one of its parts proves the frame from the caller's (`scanFrame_iff`). -/
@[mk_iff]
structure ScanFrame (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) (y : Data 32) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  two_eq : y.regs two = 2
  x_eq : y.regs xReg = x
  stored : PartialAt y.mem (y.regs tBase) τ
  fits : Fits w (y.regs tBase + 2 * n)
  pos : 1 ≤ y.regs tBase

attribute [local wram_simps] scanFrame_iff

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

/-- **The literal loop.** From `hasLit = h` and `ok = o`, the loop over the literals `ls` ends with
`hasLit = h || ls.any (litHas x b)` and `ok = o && ls.all (litOk τ x b)`, and unchanged memory. -/
theorem litLoop_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (ls : Clause (Fin n))
    (h o : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hl : HoldsList (y.regs lptr) (ls.map litCode) y.mem)
    (hend : y.regs lend = y.regs lptr + ls.length) (hh : y.regs hasLit = h.toNat)
    (ho : y.regs ok = o.toNat) (hle : Fits w (y.regs lend)) :
    ∃ z, ExecWithin w litLoop y z (14 * ls.length + 2) ∧ z.mem = y.mem ∧
      z.regs hasLit = (h || ls.any (litHas x b)).toNat ∧
      z.regs ok = (o && ls.all (litOk τ x b)).toNat ∧ z.regs lptr = y.regs lend := by
  obtain ⟨hz, h1, h2, hx, hst, hfit, hpos⟩ := hf
  wram_fold (fun rest z => ∃ h' o' : Bool, z.mem = y.mem ∧
      z.regs lptr + rest.length = y.regs lend ∧
      HoldsList (z.regs lptr) (rest.map litCode) y.mem ∧ z.regs hasLit = h'.toNat ∧
      z.regs ok = o'.toNat ∧ (h' || rest.any (litHas x b)) = (h || ls.any (litHas x b)) ∧
      (o' && rest.all (litOk τ x b)) = (o && ls.all (litOk τ x b)))
    over ls cost (fun _ => 12)
  case init => exact ⟨h, o, rfl, hend.symm, hl, hh, ho, rfl, rfl⟩
  case exit => rintro v m ⟨-, -, -, he, -⟩; omega
  case step =>
    rintro l rest v m ⟨h', o', rfl, he, hl', hh', ho', hha, hoa⟩
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp (by simpa using hl')
    refine ⟨by omega, ?_⟩
    wram_call (litBody_spec τ x b l h' o' _ ..) framed [*] with v' m' ⟨rfl, hh₁, ho₁, hp₁⟩
    exact ⟨_, _, rfl, by omega, hp₁ ▸ hrest, hh₁, ho₁,
      by rw [← hha, List.any_cons, Bool.or_assoc], by rw [← hoa, List.all_cons, Bool.and_assoc]⟩
  case post =>
    rintro v m ⟨h', o', rfl, he, -, hh', ho', hha, hoa⟩
    simp only [List.any_nil, Bool.or_false, List.all_nil, Bool.and_true] at hha hoa
    subst hha hoa
    exact ⟨by simp only [List.map_const', List.sum_replicate, smul_eq_mul]; omega, rfl, hh', ho',
      he⟩

private theorem sum_clause_cost (ψ : CNF (Fin n)) :
    (ψ.map fun c => 14 * c.length + 10 + 2).sum ≤ 14 * (encodeClauses ψ).length := by
  induction ψ with
  | nil => simp
  | cons c ψ ih =>
    simp only [List.map_cons, List.sum_cons, encodeClauses_cons, List.length_append,
      length_encodeClause]
    omega

/-- **The clause loop.** From `ptr` at the encoding of the clauses `ψ`, which end at `cEnd`, and
`fnd = f`, the loop ends with `fnd = f || ψ.any (unitTest τ x b)` and unchanged memory. -/
theorem clauseLoop_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (ψ : CNF (Fin n))
    (f : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hp : HoldsList (y.regs ptr) (encodeClauses ψ) y.mem)
    (hend : y.regs ptr + (encodeClauses ψ).length = y.regs cEnd) (hfnd : y.regs fnd = f.toNat)
    (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w clauseLoop y z (14 * (encodeClauses ψ).length + 2) ∧ z.mem = y.mem ∧
      z.regs fnd = (f || ψ.any (unitTest τ x b)).toNat := by
  obtain ⟨hz, h1, h2, hx, hst, hfit, hpos⟩ := hf
  wram_fold (fun rest z => ∃ f' : Bool, z.mem = y.mem ∧
      z.regs ptr + (encodeClauses rest).length = y.regs cEnd ∧
      HoldsList (z.regs ptr) (encodeClauses rest) y.mem ∧ z.regs fnd = f'.toNat ∧
      (f' || rest.any (unitTest τ x b)) = (f || ψ.any (unitTest τ x b)))
    over ψ cost (fun c => 14 * c.length + 10)
  case init => exact ⟨f, rfl, hend, hp, hfnd, rfl⟩
  case exit => rintro v m ⟨-, -, he, -⟩; simp only [encodeClauses_nil, List.length_nil] at he; omega
  case step =>
    rintro c rest v m ⟨f', rfl, he, hp', hfnd', hfa⟩
    rw [encodeClauses_cons] at he hp'
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hp'
    obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp (encodeClause_eq c ▸ hpc)
    simp only [List.length_append, length_encodeClause] at he hpψ
    have hu : Fits w ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat) :=
      hfit.of_le (by rw [toNat_and]; have := Bool.toNat_le (c.any (litHas x b) &&
        c.all (litOk τ x b)); omega)
    have hu' : Fits w (f'.toNat ||| ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat)) :=
      hfit.of_le (by rw [toNat_and, toNat_or]; have := Bool.toNat_le (f' ||
        (c.any (litHas x b) && c.all (litOk τ x b))); omega)
    refine ⟨by omega, ?_⟩
    unfold clauseBody clauseInit clauseDone
    wram_exec [hlen, h1, hz]
    wram_call (litLoop_spec τ x b c false true _ ..) framed [*] with v₂ m₂ ⟨rfl, hh₂, ho₂, hp₂⟩
    simp only [Bool.false_or, Bool.true_and] at hh₂ ho₂
    wram_exec [hh₂, ho₂, hfnd']
    refine ⟨f' || unitTest τ x b c, ?_⟩
    wram_simp
    exact ⟨by omega, (show v ptr + (c.length + 1) = v ptr + 1 + c.length by omega) ▸ hpψ,
      by simp [unitTest, toNat_and, toNat_or], by rw [← hfa, List.any_cons, Bool.or_assoc]⟩
  case post =>
    rintro v m ⟨f', rfl, he, -, hfnd', hfa⟩
    simp only [List.any_nil, Bool.or_false] at hfa
    subst hfa
    exact ⟨by have := sum_clause_cost ψ; omega, rfl, hfnd'⟩

/-- **The unit-clause scan.** From the clauses of `φ` stored in `[cBeg, cEnd)`, the scan reports
whether `φ` has a unit clause on `x` with polarity `b` under `τ`, within `14 E + 4` instructions,
where `E` is the length of the encoding, and leaves memory unchanged. -/
theorem unitScan_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (φ : CNF (Fin n))
    (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hcl : HoldsList (y.regs cBeg) (encodeClauses φ) y.mem)
    (hend : y.regs cBeg + (encodeClauses φ).length = y.regs cEnd) (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w unitScan y z (14 * (encodeClauses φ).length + 4) ∧ z.mem = y.mem ∧
      z.regs fnd = (φ.any (unitTest τ x b)).toNat := by
  obtain ⟨hz, h1, h2, hx, hst, hfit, hpos⟩ := hf
  refine WP.exists_execWithin ?_
  unfold unitScan
  wram_exec [hz]
  wram_call (clauseLoop_spec τ x b φ false _ ..) framed [*] with v m ⟨rfl, hfz⟩
  exact ⟨by omega, rfl, by simpa using hfz⟩

/-- **The forced value.** From the clauses of `φ` stored in `[cBeg, cEnd)` and the partial
assignment `τ` stored at `tBase`, `forcedCode` stores `optCode (forced φ τ x)` in `res` within
`28 E + 15` instructions, where `E` is the length of the encoding, and leaves memory unchanged. -/
theorem forcedCode_spec (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (y : Data 32)
    (hf : ScanFrame w τ x y) (hcl : HoldsList (y.regs cBeg) (encodeClauses φ) y.mem)
    (hend : y.regs cBeg + (encodeClauses φ).length = y.regs cEnd) (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w forcedCode y z (28 * (encodeClauses φ).length + 15) ∧ z.mem = y.mem ∧
      z.regs res = optCode (forced φ τ x) := by
  obtain ⟨hz, h1, h2, hx, hst, hfit, hpos⟩ := hf
  rw [forced_eq_ite]
  refine WP.exists_execWithin ?_
  unfold forcedCode
  wram_exec [h1]
  wram_call (unitScan_spec τ x true φ _ ..) framed [*] with v₁ m₁ ⟨rfl, hfnd₁⟩
  by_cases ht : φ.any (unitTest τ x true) = true
  · wram_exec [hfnd₁, ht, h1]
    exact ⟨by wram_simp, by wram_simp; simp [ht, optCode]⟩
  · wram_exec [hfnd₁, ht, h1, hz]
    wram_call (unitScan_spec τ x false φ _ ..) framed [*] with v₂ m₂ ⟨rfl, hfnd₂⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hf' : φ.any (unitTest τ x false) = true <;>
      wram_exec [hfnd₂, hf', h1, hz, h2] <;>
      exact ⟨by wram_simp, by wram_simp; simp [hf', optCode]⟩

end Specs

end Cslib.Algorithms.WordRAM.PPZ
