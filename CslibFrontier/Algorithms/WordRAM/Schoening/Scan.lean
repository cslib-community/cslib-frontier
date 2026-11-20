/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.Schoening
public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Algorithms.WordRAM.ClauseCode

/-!
# Finding the first falsified clause on the word RAM

A CNF formula on the variables `Fin n` is stored in word-RAM memory clause by clause: a clause
`c` occupies `c.length + 1` words, its length followed by the codes `2 v + b` of its literals
`(v, b)` (`Cslib.Algorithms.WordRAM.Schoening.encodeClause`). An assignment `σ : Fin n → Bool` is
stored as `n` words `0` or `1` (`Cslib.Algorithms.WordRAM.Schoening.AssignAt`).

`Cslib.Algorithms.WordRAM.Schoening.scan` scans the clauses in order, evaluating each one against
the stored assignment, and stops at the first falsified clause. It reports whether one was found
and, if so, the address of its encoding: exactly the clause chosen by
`Cslib.Complexity.Schoening.firstUnsat` (`Cslib.Algorithms.WordRAM.Schoening.scan_spec`). It runs
within `12 E + 4` instructions, where `E` is the number of words of the formula's encoding, and
leaves memory unchanged. The scan is the deterministic part of one step of Schöning's local search
and of the final satisfaction check.

The registers of the scan belong to a register file of 24 registers shared with the trial and
amplification programs of Schöning's algorithm (`Cslib.Algorithms.WordRAM.Schoening.Reg`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.litCode`, `Cslib.Algorithms.WordRAM.Schoening.encodeClause`,
  `Cslib.Algorithms.WordRAM.Schoening.encodeClauses`, `Cslib.Algorithms.WordRAM.Schoening.encode`:
  the word encoding of literals, clauses and formulas; the input of a trial is `n` followed by the
  clauses.
* `Cslib.Algorithms.WordRAM.Schoening.AssignAt`,
  `Cslib.Algorithms.WordRAM.Schoening.assignmentAt`: storing and reading an assignment.
* `Cslib.Algorithms.WordRAM.Schoening.ScanResult`: the result registers of the scan, matched
  against `firstUnsat`.
* `Cslib.Algorithms.WordRAM.Schoening.scan`: the scan as a structured program.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.scan_spec`: the scan finds `firstUnsat` within `12 E + 4`
  instructions without changing memory.
* `Cslib.Algorithms.WordRAM.Schoening.assignmentAt_eq`: reading back a stored assignment.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.Schoening

/-! ### Encoding -/

variable {n : ℕ}

/-- The word code `2 v + b` of the literal `(v, b)`
(`Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy` through the value of the variable). -/
def litCode (l : Literal (Fin n)) : ℕ := ClauseCode.litCodeBy Fin.val l

/-- A clause is stored as its length followed by the codes of its literals
(`Cslib.Algorithms.WordRAM.ClauseCode.encodeClauseBy`). -/
def encodeClause (c : Clause (Fin n)) : List ℕ := ClauseCode.encodeClauseBy Fin.val c

/-- The words of a clause: its length, then the codes of its literals. -/
theorem encodeClause_eq (c : Clause (Fin n)) : encodeClause c = c.length :: c.map litCode := rfl

/-- The clauses of a formula, stored one after another. -/
def encodeClauses (φ : CNF (Fin n)) : List ℕ := φ.flatMap encodeClause

/-- The input of a trial of Schöning's algorithm: the number of variables, then the clauses. -/
def encode (φ : CNF (Fin n)) : List ℕ := n :: encodeClauses φ

@[simp]
theorem length_encodeClause (c : Clause (Fin n)) : (encodeClause c).length = c.length + 1 := by
  simp [encodeClause_eq]

@[simp]
theorem encodeClauses_nil : encodeClauses ([] : CNF (Fin n)) = [] := rfl

@[simp]
theorem encodeClauses_cons (c : Clause (Fin n)) (φ : CNF (Fin n)) :
    encodeClauses (c :: φ) = encodeClause c ++ encodeClauses φ := by
  simp [encodeClauses]

/-- Literal codes are below `2 n`. -/
theorem litCode_lt (l : Literal (Fin n)) : litCode l < 2 * n := by
  obtain ⟨v, b⟩ := l
  have := v.isLt
  cases b <;> simp only [litCode, ClauseCode.litCodeBy, Bool.toNat_false,
    Bool.toNat_true] <;> omega

/-- Shifting a literal code right recovers its variable. -/
theorem litCode_shiftRight (l : Literal (Fin n)) : litCode l >>> 1 = l.1.val :=
  ClauseCode.litCodeBy_shiftRight _ _

/-- The low bit of a literal code is its sign. -/
theorem litCode_and_one (l : Literal (Fin n)) : litCode l &&& 1 = l.2.toNat :=
  ClauseCode.litCodeBy_and_one _ _

/-- The assignment `σ` is stored as the words `(σ i).toNat` from address `base`. -/
def AssignAt (mem : ℕ → ℕ) (base : ℕ) (σ : Fin n → Bool) : Prop :=
  ∀ i : Fin n, mem (base + i) = (σ i).toNat

/-- The assignment read from the `n` words at address `base`: variable `i` is true when its word
is `1`. -/
def assignmentAt (mem : ℕ → ℕ) (base n : ℕ) : Fin n → Bool :=
  fun i => decide (mem (base + i) = 1)

/-- Reading back a stored assignment. -/
theorem assignmentAt_eq {mem : ℕ → ℕ} {base : ℕ} {σ : Fin n → Bool} (h : AssignAt mem base σ) :
    assignmentAt mem base n = σ := by
  funext i
  rw [assignmentAt, h i]
  cases σ i <;> rfl

/-- One minus the XOR of two bit words is the word of their equality test. -/
theorem one_sub_toNat_xor (a b : Bool) : 1 - (a.toNat ^^^ b.toNat) = (a == b).toNat := by
  cases a <;> cases b <;> rfl

/-- The OR of two bit words is the word of their disjunction. -/
theorem toNat_or (a b : Bool) : a.toNat ||| b.toNat = (a || b).toNat := by
  cases a <;> cases b <;> rfl

/-- The XOR of two bit words is a bit. -/
theorem toNat_xor_le_one (a b : Bool) : a.toNat ^^^ b.toNat ≤ 1 := by
  cases a <;> cases b <;> decide

/-! ### Registers -/

/-! The 24 registers shared by the programs of Schöning's algorithm. -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 24 := 0
/-- Constant `1`. -/
abbrev one : Fin 24 := 1
/-- Address of the first clause. -/
abbrev cBeg : Fin 24 := 2
/-- Address of the stored assignment, which is also the end of the clauses. -/
abbrev aBase : Fin 24 := 3
/-- The number `n` of variables. -/
abbrev nReg : Fin 24 := 4
/-- Address of the current clause. -/
abbrev ptr : Fin 24 := 5
/-- Length of the current clause. -/
abbrev len : Fin 24 := 6
/-- Address of the current literal. -/
abbrev lptr : Fin 24 := 7
/-- End address of the current clause. -/
abbrev lend : Fin 24 := 8
/-- Whether the current clause has a true literal so far. -/
abbrev sat : Fin 24 := 9
/-- The current literal code. -/
abbrev lit : Fin 24 := 10
/-- The current variable. -/
abbrev var : Fin 24 := 11
/-- The sign of the current literal. -/
abbrev sgn : Fin 24 := 12
/-- Scratch address. -/
abbrev addr : Fin 24 := 13
/-- Scratch value. -/
abbrev val : Fin 24 := 14
/-- Whether a falsified clause was found. -/
abbrev found : Fin 24 := 15
/-- Address of the falsified clause found. -/
abbrev cPtr : Fin 24 := 16
/-- Loop counter. -/
abbrev cnt : Fin 24 := 17
/-- Number of steps of the local search. -/
abbrev steps : Fin 24 := 18
/-- Output. -/
abbrev out : Fin 24 := 19

end Reg

open Reg

/-! ### The scan -/

/-- One literal: read its code, look up its variable, and record whether it is true. -/
def litBody : Code .standard 24 := ram[
  lit ← *lptr; var ← lit >>> one; sgn ← lit &&& one; addr ← aBase + var; val ← *addr;
  addr ← val ^^^ sgn; addr ← one - addr; sat ← sat ||| addr; lptr ← lptr + one ]

/-- Evaluate the literals in `[lptr, lend)`. -/
def litLoop : Code .standard 24 := .loop (.lt lptr lend) litBody

/-- Read the length of the clause at `ptr` and set up its literal loop. -/
def clauseInit : Code .standard 24 := ram[
  len ← *ptr; lptr ← ptr + one; lend ← lptr + len; sat ← zero ]

/-- After a clause: on a falsified clause record it and jump to the end, otherwise move on. -/
def clauseDone : Code .standard 24 := ram[
  if sat = zero then [ found ← one; cPtr ← ptr; ptr ← aBase ] else [ ptr ← lend ] ]

/-- One clause: evaluate it, and on a falsified clause record it and jump to the end. -/
def clauseBody : Code .standard 24 := ram[ ⟪clauseInit⟫; ⟪litLoop⟫; ⟪clauseDone⟫ ]

/-- Evaluate the clauses in `[ptr, aBase)` until a falsified one. -/
def clauseLoop : Code .standard 24 := .loop (.lt ptr aBase) clauseBody

/-- **The scan**: find the first clause falsified by the stored assignment. -/
def scan : Code .standard 24 := ram[ ptr ← cBeg; found ← zero; ⟪clauseLoop⟫ ]

/-- The result registers of the scan: no falsified clause, or the address `cptr` of the encoding
of the first one, which ends by address `e`. -/
def ScanResult (σ : Fin n → Bool) (φ : CNF (Fin n)) (mem : ℕ → ℕ) (e fnd cptr : ℕ) : Prop :=
  match firstUnsat φ σ with
  | none => fnd = 0
  | some c => fnd = 1 ∧ HoldsList cptr (encodeClause c) mem ∧ cptr + c.length + 1 ≤ e

/-- The cons equation of `firstUnsat`: `List.find?_cons` with the match on `!c.eval σ` stated as an
`if`, the form the scan proofs rewrite with. -/
theorem firstUnsat_cons (σ : Fin n → Bool) (c : Clause (Fin n)) (φ : CNF (Fin n)) :
    firstUnsat (c :: φ) σ = if c.eval σ then firstUnsat φ σ else some c := by
  cases h : c.eval σ <;> simp [firstUnsat, h]

/-- `firstUnsat` finds nothing exactly on satisfying assignments. -/
theorem firstUnsat_eq_none_iff (σ : Fin n → Bool) (φ : CNF (Fin n)) :
    firstUnsat φ σ = none ↔ φ.eval σ = true := by
  induction φ with
  | nil => simp [firstUnsat]
  | cons c φ ih =>
    rw [firstUnsat_cons, CNF.eval_cons]
    cases c.eval σ <;> simp [ih]

/-- A satisfied first clause does not change the scan result. -/
theorem scanResult_cons_of_eval {σ : Fin n → Bool} {c : Clause (Fin n)} {ψ : CNF (Fin n)}
    (h : c.eval σ = true) : ScanResult σ (c :: ψ) = ScanResult σ ψ := by
  funext mem e fnd cptr
  simp only [ScanResult, firstUnsat_cons, h, ↓reduceIte]

section Specs

variable {w : ℕ}

/-- **The literal loop.** Starting from `sat = s`, the loop over the literals `ls` ends with
`sat = s || ls.eval σ`, `lptr = lend`, and unchanged memory. -/
theorem litLoop_spec (σ : Fin n → Bool) (ls : Clause (Fin n)) (x : Data 24) (s : Bool)
    (hone : x.regs one = 1) (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hend : x.regs lend = x.regs lptr + ls.length) (hs : x.regs sat = s.toNat)
    (hσ : AssignAt x.mem (x.regs aBase) σ) (hle : x.regs lend ≤ x.regs aBase + 2 * n)
    (hw : Fits w (x.regs aBase + 2 * n)) (hpos : 1 ≤ x.regs aBase + 2 * n) :
    ∃ y, ExecWithin w litLoop x y (11 * ls.length + 2) ∧ y.mem = x.mem ∧
      y.regs sat = (s || Clause.eval σ ls).toNat ∧ y.regs lptr = x.regs lend ∧
      y.regs aBase = x.regs aBase ∧ y.regs one = 1 := by
  induction ls generalizing x s with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), rfl, by simp [hs], by simp [hend],
      rfl, hone⟩
    simp [Cond.holds_lt, hend]
  | cons l ls ih =>
    simp only [List.length_cons] at hend
    have hc : (Cond.lt lptr lend).Holds x := by simp only [Cond.holds_lt, hend]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp hl
    have hlv : l.1.val < n := l.1.isLt
    have : Fits w l.1.val := hw.of_le (by omega)
    have : Fits w l.2.toNat := hw.of_le (by have := Bool.toNat_le l.2; omega)
    have : Fits w ((σ l.1).toNat ^^^ l.2.toNat) :=
      hw.of_le (by have := toNat_xor_le_one (σ l.1) l.2; omega)
    have : Fits w (σ l.1 == l.2).toNat :=
      hw.of_le (by have := Bool.toNat_le (σ l.1 == l.2); omega)
    have : Fits w (s || (σ l.1 == l.2)).toNat :=
      hw.of_le (by have := Bool.toNat_le (s || (σ l.1 == l.2)); omega)
    have : Fits w (x.regs lptr + 1) := hw.of_le (by omega)
    have hxor : (σ l.1).toNat ^^^ l.2.toNat ≤ 1 := toNat_xor_le_one (σ l.1) l.2
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold litBody
    wram_exec [hone, hlit, litCode_shiftRight, litCode_and_one, hσ l.1, hs,
      one_sub_toNat_xor, toNat_or]
    wram_call (ih _ (s || (σ l.1 == l.2)) (by wram_simp [hone]) (by wram_simp; exact hrest)
      (by wram_simp [hend]; omega) (by wram_simp) (by wram_simp; exact hσ)
      (by wram_simp; omega) (by wram_simp; exact hw) (by wram_simp; exact hpos))
      with y ⟨hym, hys, hyp, hya, hyo⟩
    refine ⟨by simp only [List.length_cons]; omega, hym, ?_,
      by wram_simp at hyp; exact hyp, by wram_simp at hya; exact hya, hyo⟩
    rw [hys, Clause.eval_cons, Literal.eval, Bool.or_assoc]

/-- **The clause loop.** From `ptr` at the encoding of the clauses `ψ`, which end at `aBase`, and
`found = 0`, the loop ends with the scan result for `ψ` and unchanged memory. -/
theorem clauseLoop_spec (σ : Fin n → Bool) (ψ : CNF (Fin n)) (x : Data 24)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hp : HoldsList (x.regs ptr) (encodeClauses ψ) x.mem)
    (hend : x.regs ptr + (encodeClauses ψ).length = x.regs aBase) (hfound : x.regs found = 0)
    (hσ : AssignAt x.mem (x.regs aBase) σ)
    (hw : Fits w (x.regs aBase + 2 * n)) (hpos : 1 ≤ x.regs aBase + 2 * n) :
    ∃ y, ExecWithin w clauseLoop x y (12 * (encodeClauses ψ).length + 2) ∧ y.mem = x.mem ∧
      ScanResult σ ψ x.mem (x.regs aBase) (y.regs found) (y.regs cPtr) := by
  induction ψ generalizing x with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono le_rfl, rfl, by simp [ScanResult, firstUnsat, hfound]⟩
    simp only [encodeClauses_nil, List.length_nil, Nat.add_zero] at hend
    simp [Cond.holds_lt, hend]
  | cons c ψ ih =>
    rw [encodeClauses_cons] at hp hend
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hp
    simp only [List.length_append, length_encodeClause] at hend hpψ
    obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp (encodeClause_eq c ▸ hpc)
    have hc : (Cond.lt ptr aBase).Holds x := by simp only [Cond.holds_lt]; omega
    have : Fits w (x.regs ptr + 1) := hw.of_le (by omega)
    have : Fits w (x.regs ptr + 1 + c.length) := hw.of_le (by omega)
    have : Fits w 1 := hw.of_le hpos
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold clauseBody clauseInit
    wram_exec [hlen, hone, hzero]
    refine WP.name fun x₁ hx₁ => ?_
    obtain ⟨x₂, hlit, hm₂, hs₂, hp₂, ha₂, ho₂⟩ := litLoop_spec (w := w) σ c x₁ false
      (by subst hx₁; wram_simp [hone]) (by subst hx₁; wram_simp; exact hlits)
      (by subst hx₁; wram_simp) (by subst hx₁; wram_simp; rfl)
      (by subst hx₁; wram_simp; exact hσ) (by subst hx₁; wram_simp; omega)
      (by subst hx₁; wram_simp; exact hw) (by subst hx₁; wram_simp; exact hpos)
    have hz₂ : x₂.regs zero = 0 :=
      (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hzero])
    have hptr₂ : x₂.regs ptr = x.regs ptr :=
      (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp)
    have hlend₂ : x₂.regs lend = x.regs ptr + 1 + c.length :=
      (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp)
    have hfound₂ : x₂.regs found = 0 :=
      (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hfound])
    subst hx₁
    wram_simp at ha₂
    simp only [Data.set_mem, Bool.false_or] at hm₂ hs₂
    refine WP.of_execWithin hlit ?_
    unfold clauseDone
    cases hce : c.eval σ with
    | false =>
      simp only [hce, Bool.toNat_false] at hs₂
      wram_exec [hs₂, hz₂, ho₂, hptr₂, ha₂]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, ha₂]))
        ⟨?_, hm₂, ?_⟩
      · simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
      · wram_simp [ScanResult, firstUnsat_cons, hce]
        exact ⟨hpc, by omega⟩
    | true =>
      simp only [hce, Bool.toNat_true] at hs₂
      wram_exec [hs₂, hz₂, hlend₂]
      wram_call (ih _ (by wram_simp [hz₂]) (by wram_simp [ho₂])
        (by
          wram_simp
          simpa only [hm₂, show x.regs ptr + 1 + c.length = x.regs ptr + (c.length + 1) by omega]
            using hpψ)
        (by wram_simp; rw [ha₂]; omega) (by wram_simp [hfound₂])
        (by wram_simp; rw [hm₂, ha₂]; exact hσ) (by wram_simp; rw [ha₂]; exact hw)
        (by wram_simp; rw [ha₂]; exact hpos))
        with y ⟨hym, hyr⟩
      refine ⟨?_, by simpa [hm₂] using hym, ?_⟩
      · simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
      · rw [scanResult_cons_of_eval hce]
        wram_simp [hm₂, ha₂] at hyr
        exact hyr

/-- **The scan.** From the clauses of `φ` stored in `[cBeg, aBase)` and the assignment `σ` stored at
`aBase`, the scan reports `firstUnsat φ σ` within `12 E + 4` instructions, where `E` is the length
of the encoding, and leaves memory unchanged. -/
theorem scan_spec (σ : Fin n → Bool) (φ : CNF (Fin n)) (x : Data 24)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcl : HoldsList (x.regs cBeg) (encodeClauses φ) x.mem)
    (hend : x.regs cBeg + (encodeClauses φ).length = x.regs aBase)
    (hσ : AssignAt x.mem (x.regs aBase) σ)
    (hw : Fits w (x.regs aBase + 2 * n)) (hpos : 1 ≤ x.regs aBase + 2 * n) :
    ∃ y, ExecWithin w scan x y (12 * (encodeClauses φ).length + 4) ∧ y.mem = x.mem ∧
      ScanResult σ φ x.mem (x.regs aBase) (y.regs found) (y.regs cPtr) := by
  refine WP.exists_execWithin ?_
  unfold scan
  wram_exec [hzero]
  wram_call (clauseLoop_spec (w := w) σ φ _ (by wram_simp [hzero]) (by wram_simp [hone])
    (by wram_simp; exact hcl) (by wram_simp [hend]) (by wram_simp) (by wram_simp; exact hσ)
    (by wram_simp; exact hw) (by wram_simp; exact hpos))
    with y ⟨hym, hyr⟩
  exact ⟨by omega, hym, by wram_simp at hyr; exact hyr⟩

end Specs

end Cslib.Algorithms.WordRAM.Schoening

end
