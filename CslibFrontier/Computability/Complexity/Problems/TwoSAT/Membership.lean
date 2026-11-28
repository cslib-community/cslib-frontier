/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT.Routines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Relation.RelatesWithinSteps

/-!
# The complement of 2SAT in nondeterministic logarithmic space

A nondeterministic counter program (`Cslib.Complexity.TwoSAT.decider`) accepts, on the encoding
of a formula `φ`, exactly when `φ ∉ TwoSAT` (`Cslib.Complexity.TwoSAT.accepts_decider_iff`). It
first guesses which of two reasons to look for:

* a clause that is empty or has more than two literals: it guesses the clause and counts its
  literals;
* a variable `x` with a path from `x` to `¬x` and one back in the implication graph
  (`Cslib.Logic.PL.CNF.Implies`) [Papadimitriou, Theorem 16.3][Papadimitriou94]: it guesses an
  occurrence of `x` and walks from `x`, first to `¬x` and then back to `x`, giving up after as
  many steps as the input has bits in each half.

These are all the reasons (`Cslib.Complexity.notMem_TwoSAT_iff`), by the theorem of Aspvall,
Plass and Tarjan [AspvallPlassTarjan1979]. The walk stores its current literal as the position of
an occurrence of its variable and a polarity. A step guesses a clause and one of its literals
`ℓ'`, checks that the clause has one or two literals and that its other literal, or `ℓ'` itself
for a unit clause, is the negation of the current literal, which is the arc from the current
literal to `ℓ'` of the implication graph, and moves to `ℓ'`. Variables are compared digit by
digit through their positions (`Cslib.Complexity.TwoSAT.cmpVarCode`), so only positions,
counters and flags are stored, all at most the length of the input. The strategy, guessing the
two paths, is that of [Papadimitriou, Theorem 16.3][Papadimitriou94]; the program, its register
layout and the positional comparison of variables are this library's own.

## Main definitions

* `Cslib.Complexity.TwoSAT.decider`: the nondeterministic counter program.

## Main results

* `Cslib.Complexity.TwoSAT.accepts_decider_iff`: it accepts exactly the formulas outside
  `TwoSAT`.
* `Cslib.Complexity.TwoSAT.exists_decidesInLogSpace_compl`: one nondeterministic machine decides
  the complement of `TwoSAT` in logarithmic space, every branch halting.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Theorem 16.3][Papadimitriou94]
* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
-/

@[expose] public section

namespace Cslib.Complexity

namespace TwoSAT

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr Cslib.Logic.PL

/-- **The decider of the complement of `TwoSAT`.** Register `0` holds the choice, register `1` a
scanning position, registers `2`, `3` and `4` the occurrence of the starting variable, the
occurrence of the current variable and the current polarity, registers `5`, `6` and `7` the
phase, the number of steps and the length of the input, registers `8` to `10` the literals of a
guessed clause, registers `11` and `12` the next literal and the other one, and registers `13`
to `15` cursors. Label `102` accepts and label `103` rejects. -/
def decider : CounterProgram where
  code := List.flatten [
    -- 0, 1: count the input; 2: guess the reason
    [read (reg 7) 1 1 2,
     assign 7 (add (reg 7) (const 1)) 0,
     lt (reg 0) (const 1) 3 20,
    -- 3 to 19: a clause of width zero or more than two
     read (reg 1) 4 4 103,
     lt (reg 0) (const 1) 10 5],
    skipClauseCode 5 1 3,
    [assign 8 (reg 1) 11,
     read (reg 8) 12 102 102],
    skipLitCode 12 8 15,
    [read (reg 8) 16 103 103],
    skipLitCode 16 8 19,
    [read (reg 8) 102 103 103,
    -- 20 to 34: the occurrence of the starting variable
     read (reg 1) 21 21 103,
     lt (reg 0) (const 1) 27 22],
    skipClauseCode 22 1 20,
    [read (reg 1) 28 103 103,
     lt (reg 0) (const 1) 32 29],
    skipLitCode 29 1 27,
    [assign 2 (reg 1) 33,
     assign 3 (reg 1) 34,
     assign 4 (const 1) 35],
    -- 35 to 51: the end of a half of the walk, and the number of steps
    cmpVarCode 35 3 2 13 14 45 50,
    [lt (reg 4) (const 1) 46 47,
     lt (reg 5) (const 1) 48 50,
     lt (reg 5) (const 1) 50 102,
     assign 5 (const 1) 49,
     assign 6 (const 0) 50,
     lt (reg 6) (reg 7) 51 103,
     assign 6 (add (reg 6) (const 1)) 52,
    -- 52 to 78: a clause and its literals
     assign 1 (const 0) 53,
     read (reg 1) 54 54 103,
     lt (reg 0) (const 1) 60 55],
    skipClauseCode 55 1 53,
    [assign 8 (reg 1) 61,
     read (reg 8) 62 103 103,
     assign 9 (reg 8) 63],
    skipLitCode 63 9 66,
    [read (reg 9) 69 67 67,
     assign 11 (reg 8) 68,
     assign 12 (reg 8) 79,
     assign 10 (reg 9) 70],
    skipLitCode 70 10 73,
    [read (reg 10) 103 74 74,
     lt (reg 0) (const 1) 75 77,
     assign 11 (reg 8) 76,
     assign 12 (reg 9) 79,
     assign 11 (reg 9) 78,
     assign 12 (reg 8) 79],
    -- 79 to 101: the arc, and the move
    cmpVarCode 79 12 3 13 14 89 103,
    signCode 89 12 15 93 94,
    [lt (reg 4) (const 1) 95 103,
     lt (reg 4) (const 1) 103 95,
     assign 3 (reg 11) 96],
    signCode 96 11 15 100 101,
    [assign 4 (const 1) 35,
     assign 4 (const 0) 35,
     accept,
     reject]]
  registers := 16

theorem length_code_decider : decider.code.length = 104 := rfl

/-! ### Registers -/

/-- The registers other than the choice. -/
structure St where
  /-- Register `1`. -/
  p : ℕ := 0
  /-- Register `2`. -/
  o₀ : ℕ := 0
  /-- Register `3`. -/
  cur : ℕ := 0
  /-- Register `4`. -/
  sgn : ℕ := 0
  /-- Register `5`. -/
  phase : ℕ := 0
  /-- Register `6`. -/
  steps : ℕ := 0
  /-- Register `7`. -/
  len : ℕ := 0
  /-- Register `8`. -/
  q₁ : ℕ := 0
  /-- Register `9`. -/
  q₂ : ℕ := 0
  /-- Register `10`. -/
  q₃ : ℕ := 0
  /-- Register `11`. -/
  o₁ : ℕ := 0
  /-- Register `12`. -/
  o₂ : ℕ := 0
  /-- Register `13`. -/
  t₁ : ℕ := 0
  /-- Register `14`. -/
  t₂ : ℕ := 0
  /-- Register `15`. -/
  t : ℕ := 0

/-- The registers, with the choice `c`. -/
def St.regs (st : St) (c : ℕ) : List ℕ :=
  [c, st.p, st.o₀, st.cur, st.sgn, st.phase, st.steps, st.len, st.q₁, st.q₂, st.q₃, st.o₁, st.o₂,
    st.t₁, st.t₂, st.t]

/-- All registers other than the choice are at most `B`. -/
def St.Bounded (B : ℕ) (st : St) : Prop :=
  st.p ≤ B ∧ st.o₀ ≤ B ∧ st.cur ≤ B ∧ st.sgn ≤ B ∧ st.phase ≤ B ∧ st.steps ≤ B ∧ st.len ≤ B ∧
    st.q₁ ≤ B ∧ st.q₂ ≤ B ∧ st.q₃ ≤ B ∧ st.o₁ ≤ B ∧ st.o₂ ≤ B ∧ st.t₁ ≤ B ∧ st.t₂ ≤ B ∧ st.t ≤ B

theorem St.forall_mem_regs {B : ℕ} {st : St} {c : ℕ} (h : st.Bounded B) (hc : c ≤ B) :
    ∀ r ∈ st.regs c, r ≤ B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  simp only [St.regs, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl) <;> assumption

@[simp]
theorem withChoice_regs (l : ℕ) (st : St) (c : ℕ) (b : Bool) :
    withChoice (l, st.regs c) b = (l, st.regs b.toNat) := by
  simp [withChoice, St.regs]

@[simp] theorem length_regs (st : St) (c : ℕ) : (st.regs c).length = 16 := rfl

@[simp] theorem St.getD_regs_1 (st : St) (c : ℕ) : (st.regs c).getD 1 0 = st.p := rfl
@[simp] theorem St.set_regs_1 (st : St) (c x : ℕ) :
    (st.regs c).set 1 x = { st with p := x }.regs c := rfl
@[simp] theorem St.getD_regs_2 (st : St) (c : ℕ) : (st.regs c).getD 2 0 = st.o₀ := rfl
@[simp] theorem St.set_regs_2 (st : St) (c x : ℕ) :
    (st.regs c).set 2 x = { st with o₀ := x }.regs c := rfl
@[simp] theorem St.getD_regs_3 (st : St) (c : ℕ) : (st.regs c).getD 3 0 = st.cur := rfl
@[simp] theorem St.set_regs_3 (st : St) (c x : ℕ) :
    (st.regs c).set 3 x = { st with cur := x }.regs c := rfl
@[simp] theorem St.getD_regs_4 (st : St) (c : ℕ) : (st.regs c).getD 4 0 = st.sgn := rfl
@[simp] theorem St.set_regs_4 (st : St) (c x : ℕ) :
    (st.regs c).set 4 x = { st with sgn := x }.regs c := rfl
@[simp] theorem St.getD_regs_5 (st : St) (c : ℕ) : (st.regs c).getD 5 0 = st.phase := rfl
@[simp] theorem St.set_regs_5 (st : St) (c x : ℕ) :
    (st.regs c).set 5 x = { st with phase := x }.regs c := rfl
@[simp] theorem St.getD_regs_6 (st : St) (c : ℕ) : (st.regs c).getD 6 0 = st.steps := rfl
@[simp] theorem St.set_regs_6 (st : St) (c x : ℕ) :
    (st.regs c).set 6 x = { st with steps := x }.regs c := rfl
@[simp] theorem St.getD_regs_7 (st : St) (c : ℕ) : (st.regs c).getD 7 0 = st.len := rfl
@[simp] theorem St.set_regs_7 (st : St) (c x : ℕ) :
    (st.regs c).set 7 x = { st with len := x }.regs c := rfl
@[simp] theorem St.getD_regs_8 (st : St) (c : ℕ) : (st.regs c).getD 8 0 = st.q₁ := rfl
@[simp] theorem St.set_regs_8 (st : St) (c x : ℕ) :
    (st.regs c).set 8 x = { st with q₁ := x }.regs c := rfl
@[simp] theorem St.getD_regs_9 (st : St) (c : ℕ) : (st.regs c).getD 9 0 = st.q₂ := rfl
@[simp] theorem St.set_regs_9 (st : St) (c x : ℕ) :
    (st.regs c).set 9 x = { st with q₂ := x }.regs c := rfl
@[simp] theorem St.getD_regs_10 (st : St) (c : ℕ) : (st.regs c).getD 10 0 = st.q₃ := rfl
@[simp] theorem St.set_regs_10 (st : St) (c x : ℕ) :
    (st.regs c).set 10 x = { st with q₃ := x }.regs c := rfl
@[simp] theorem St.getD_regs_11 (st : St) (c : ℕ) : (st.regs c).getD 11 0 = st.o₁ := rfl
@[simp] theorem St.set_regs_11 (st : St) (c x : ℕ) :
    (st.regs c).set 11 x = { st with o₁ := x }.regs c := rfl
@[simp] theorem St.getD_regs_12 (st : St) (c : ℕ) : (st.regs c).getD 12 0 = st.o₂ := rfl
@[simp] theorem St.set_regs_12 (st : St) (c x : ℕ) :
    (st.regs c).set 12 x = { st with o₂ := x }.regs c := rfl
@[simp] theorem St.getD_regs_13 (st : St) (c : ℕ) : (st.regs c).getD 13 0 = st.t₁ := rfl
@[simp] theorem St.set_regs_13 (st : St) (c x : ℕ) :
    (st.regs c).set 13 x = { st with t₁ := x }.regs c := rfl
@[simp] theorem St.getD_regs_14 (st : St) (c : ℕ) : (st.regs c).getD 14 0 = st.t₂ := rfl
@[simp] theorem St.set_regs_14 (st : St) (c x : ℕ) :
    (st.regs c).set 14 x = { st with t₂ := x }.regs c := rfl
@[simp] theorem St.getD_regs_15 (st : St) (c : ℕ) : (st.regs c).getD 15 0 = st.t := rfl
@[simp] theorem St.set_regs_15 (st : St) (c x : ℕ) :
    (st.regs c).set 15 x = { st with t := x }.regs c := rfl
@[simp] theorem St.getD_regs_0 (st : St) (c : ℕ) : (st.regs c).getD 0 0 = c := rfl

/-! ### Halting -/

theorem reject_ne_accept : (Instr.reject : Instr) ≠ Instr.accept := nofun

variable (φ : CNF ℕ)

/-- What every halt guarantees: accepting only formulas outside `TwoSAT`. -/
def Post (s : Config) : Prop := decider.instr s.1 = .accept → φ ∉ TwoSAT

/-- The bound on the registers: the length of the input, plus one for the choice. -/
abbrev bnd : ℕ := (encCNF φ).length + 1

variable {φ}

private theorem mem_regs_le {st : St} (hB : st.Bounded (bnd φ)) (b : Bool) :
    ∀ r ∈ st.regs b.toNat, r ≤ bnd φ :=
  st.forall_mem_regs hB (by cases b <;> exact Nat.le_add_left _ _)

private theorem mem_regs_zero {st : St} (hB : st.Bounded (bnd φ)) :
    ∀ r ∈ st.regs 0, r ≤ bnd φ :=
  st.forall_mem_regs hB (Nat.zero_le _)

private theorem one_le_bnd : 1 ≤ bnd φ :=
  Nat.le_add_left _ _

attribute [local cp_simps]
  St.getD_regs_0 St.getD_regs_1 St.getD_regs_2 St.getD_regs_3 St.getD_regs_4 St.getD_regs_5
  St.getD_regs_6 St.getD_regs_7 St.getD_regs_8 St.getD_regs_9 St.getD_regs_10 St.getD_regs_11
  St.getD_regs_12 St.getD_regs_13 St.getD_regs_14 St.getD_regs_15

/-- Every branch from the rejecting halt. -/
theorem ab_reject {Q : Config → Prop} {st : St} (hB : st.Bounded (bnd φ)) (b : Bool) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (103, st.regs b.toNat) :=
  .halt rfl (fun h => absurd h reject_ne_accept) (mem_regs_le hB b)

/-- Every branch from the accepting halt, for a formula outside `TwoSAT`. -/
theorem ab_accept {Q : Config → Prop} {st : St} (hB : st.Bounded (bnd φ)) (b : Bool)
    (h : φ ∉ TwoSAT) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (102, st.regs b.toNat) :=
  .halt rfl (fun _ => h) (mem_regs_le hB b)

/-- A step to the rejecting halt. -/
theorem ab_step_reject {Q : Config → Prop} {l : ℕ} {st : St} (hB : st.Bounded (bnd φ))
    (hh : decider.halted (l, st.regs 0) = false) (b : Bool)
    (hstep : ∀ b : Bool, decider.step (encCNF φ) (l, st.regs b.toNat) = (103, st.regs b.toNat)) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (l, st.regs b.toNat) :=
  .step hh (mem_regs_le hB b) fun b' => by simpa [hstep] using ab_reject hB b'

/-! ### Code placement -/

theorem codeAt_skipClause₅ : decider.CodeAt 5 (skipClauseCode 5 1 3) := codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_skipLit₁₂ : decider.CodeAt 12 (skipLitCode 12 8 15) := codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_skipLit₁₆ : decider.CodeAt 16 (skipLitCode 16 8 19) := codeAt_of_prefix ⟨_, rfl⟩

/-! ### A clause of width zero or more than two -/

/-- A position within the input is at most the bound. -/
theorem le_bnd_of_infixAt {p : ℕ} {u : List Bool} (h : InfixAt (encCNF φ) p u) (hu : u ≠ []) :
    p + u.length ≤ bnd φ :=
  Nat.le_succ_of_le (h.le_length hu)

theorem literalBits_ne_nil (v : ℕ) (b : Bool) : literalBits v b ≠ [] := by
  simp [literalBits]

/-- Bounds survive an update of registers. -/
local macro "st_bounded" : tactic => `(tactic| (
  simp only [St.Bounded, bnd] at *
  and_intros <;> first | assumption | omega))

private theorem reaches_read_skipLit₈ {l next bad ret q x : ℕ} {m : Literal ℕ}
    (hl : decider.instr l = .read (reg 8) next bad bad)
    (hcode : decider.CodeAt next (skipLitCode next 8 ret))
    (hm : InfixAt (encCNF φ) q (literalBits m.1 m.2)) {st : St} (hq : st.q₁ = q)
    (hB : st.Bounded (bnd φ)) (hx : x ≤ bnd φ) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (l, st.regs x)
      (ret, ({ st with q₁ := q + (literalBits m.1 m.2).length } : St).regs x) := by
  have hend := le_bnd_of_infixAt hm (literalBits_ne_nil _ _)
  have hregs := st.forall_mem_regs hB hx
  cp_step [hq, hm.literal_start]
  simpa [hq, St.set_regs_8] using reaches_skipLitCode hcode (by omega) (by simp) hm
    (St.getD_regs_8 st x ▸ hq) hregs hend

/-- Checking from label `15` whether a clause with at least two literals has a third literal. -/
private theorem reaches_width_two {q : ℕ} {m₁ m₂ : Literal ℕ} {rest : Clause ℕ}
    (hrest : LitsAt (encCNF φ) q (m₂ :: rest)) {st : St} (hB : st.Bounded (bnd φ))
    (x : ℕ) (hx : x ≤ bnd φ) :
    ∃ st' : St, st'.Bounded (bnd φ) ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ))
        (15, ({ st with q₁ := q } : St).regs x)
        (if (m₁ :: m₂ :: rest).length = 0 ∨ 3 ≤ (m₁ :: m₂ :: rest).length then 102 else 103,
          st'.regs x) := by
  obtain ⟨hm₂, hrest₂⟩ := hrest.cons
  have hend₂ := le_bnd_of_infixAt hm₂ (literalBits_ne_nil _ _)
  have hB₂ : ({ st with q₁ := q + (literalBits m₂.1 m₂.2).length } : St).Bounded (bnd φ) := by
    st_bounded
  refine ⟨_, hB₂,
    (reaches_read_skipLit₈ (l := 15) rfl codeAt_skipLit₁₆ hm₂ rfl (by st_bounded) hx).trans ?_⟩
  have := St.forall_mem_regs hB₂ hx
  rcases rest with _ | ⟨m₃, rest⟩
  · change decider.Reaches _ _ _ (103, _)
    cp_step [hrest₂.getElem?_nil]
  · change decider.Reaches _ _ _ (102, _)
    cp_step [hrest₂.cons.1.literal_start]

/-- **The width of a clause**: from label `10`, the run accepts exactly when the clause at the
scanning position is empty or has more than two literals. -/
theorem reaches_width {p : ℕ} {c : Clause ℕ} (hc : LitsAt (encCNF φ) p c) {st : St}
    (hp : st.p = p) (hB : st.Bounded (bnd φ)) (x : ℕ) (hx : x ≤ bnd φ) :
    ∃ st' : St, st'.Bounded (bnd φ) ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (10, st.regs x)
        (if c.length = 0 ∨ 3 ≤ c.length then 102 else 103, st'.regs x) := by
  subst hp
  have hB₁ : ∀ q ≤ bnd φ, ({ st with q₁ := q } : St).Bounded (bnd φ) := fun q hq => by st_bounded
  have h₁₀ : decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (10, st.regs x)
      (11, ({ st with q₁ := st.p } : St).regs x) := by
    have := st.forall_mem_regs hB hx
    cp_step [St.set_regs_8]
  rcases c with _ | ⟨m₁, _ | ⟨m₂, rest⟩⟩
  · refine ⟨{ st with q₁ := st.p }, hB₁ st.p hB.1, h₁₀.trans ?_⟩
    have := St.forall_mem_regs (hB₁ st.p hB.1) hx
    change decider.Reaches _ _ _ (102, _)
    cp_step [hc.getElem?_nil]
  all_goals
    obtain ⟨hm₁, hrest⟩ := hc.cons
    have hend₁ := le_bnd_of_infixAt hm₁ (literalBits_ne_nil _ _)
    have hread₁ := h₁₀.trans (reaches_read_skipLit₈ (l := 11) rfl codeAt_skipLit₁₂ hm₁ rfl
      (hB₁ st.p hB.1) hx)
  · refine ⟨_, hB₁ _ (by omega), hread₁.trans ?_⟩
    have := St.forall_mem_regs (hB₁ _ (by omega)) hx
    change decider.Reaches _ _ _ (103, _)
    cp_step [hrest.getElem?_nil]
  · obtain ⟨st', hB', h₂⟩ := reaches_width_two (m₁ := m₁) hrest hB x hx
    exact ⟨st', hB', hread₁.trans h₂⟩

/-! ### Every branch through the decider -/

/-- Reading the scanning position `p` in register `1` at label `l`. -/
private theorem reaches_read_p {l yes no e : ℕ} (hl : decider.instr l = read (reg 1) yes no e)
    {st : St} {p : ℕ} (hp : st.p = p) (hB : st.Bounded (bnd φ)) {l' : ℕ}
    (h : readLabel yes no e (encCNF φ)[p]? = l') :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (l, st.regs 0) (l', st.regs 0) := by
  subst hp; subst h
  have := mem_regs_zero hB
  rcases hbit : (encCNF φ)[st.p]? with _ | _ | _ <;> simp only [readLabel] <;> cp_step [hbit]

/-- Every branch through deterministic code, then from its end. -/
theorem ab_of_reaches {Q : Config → Prop} {l l' : ℕ} {st st' : St} {x : ℕ}
    (h : decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (l, st.regs x) (l', st'.regs x))
    (hcont : ∀ b : Bool, decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (l', st'.regs b.toNat))
    (b : Bool) : decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (l, st.regs b.toNat) := by
  simpa only [withChoice_regs] using (allBranches_of_oblivious (Post := Post φ)
    (Q := fun s => ∃ b : Bool, s = (l', st'.regs b.toNat)) (by simp [bnd]) h
    (fun c => ⟨c, by simp⟩) b).bind fun _ ⟨b', hb'⟩ => hb' ▸ hcont b'

/-- A step at a choice: `yes` for the choice `0` and `no` for the choice `1`. -/
theorem ab_choice {Q : Config → Prop} {l yes no : ℕ} {st : St}
    (hl : decider.instr l = lt (reg 0) (const 1) yes no) (hB : st.Bounded (bnd φ))
    (hyes : ∀ b : Bool, decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (yes, st.regs b.toNat))
    (hno : ∀ b : Bool, decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (no, st.regs b.toNat))
    (b : Bool) : decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q (l, st.regs b.toNat) := by
  refine .step (by simp [halted, hl, Instr.halts]) (mem_regs_le hB b) fun b' => ?_
  rw [step_lt _ _ hl]
  simp only [eval_reg, St.getD_regs_0, eval_const, withChoice_regs]
  cases b
  · simpa using hyes b'
  · simpa using hno b'

/-- The first bit of a clause is that of its first literal, or the end of the clause. -/
theorem LitsAt.getElem?_isSome {w : List Bool} {p : ℕ} {c : Clause ℕ} (h : LitsAt w p c) :
    ∃ b, w[p]? = some b := by
  rcases c with _ | ⟨m, c⟩
  · exact ⟨false, h.getElem?_nil⟩
  · exact ⟨true, h.cons.1.literal_start⟩

theorem readLabel_some (yes no e : ℕ) {o : Option Bool} (h : ∃ b, o = some b) (hyn : yes = no) :
    readLabel yes no e o = yes := by
  obtain ⟨b, rfl⟩ := h
  cases b <;> simp [readLabel, hyn]

/-- The length of the bits of a clause. -/
theorem length_clauseBits (c : Clause ℕ) :
    (clauseBits c).length = (c.flatMap fun l => literalBits l.1 l.2).length + 1 := by
  simp [clauseBits]

private theorem reaches_skip_clause_p {skip ret p : ℕ} {c : Clause ℕ}
    (hskip : decider.CodeAt skip (skipClauseCode skip 1 ret)) (hc : LitsAt (encCNF φ) p c)
    {st : St} (hp : st.p = p) (hB : st.Bounded (bnd φ)) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (skip, st.regs 0)
      (ret, ({ st with p := p + (c.flatMap fun l => literalBits l.1 l.2).length + 1 } : St).regs
        0) := by
  have hl := hc.le_length
  simpa [St.set_regs_1] using reaches_skipClauseCode hskip (by omega) (by simp) hc
    (St.getD_regs_1 st 0 ▸ hp) (mem_regs_zero hB) (by simp only [bnd]; omega)

/-- **Every branch of a clause-scanning loop**, from the clauses `cs`: the code at `l₀` reads the
scanning position, rejecting at the end of the input, and the choice at `l₀ + 1` inspects the
clause there at `inspect` or skips it with the code at `skip`. Only the scanning position changes
along the loop. -/
private theorem ab_scanLoop {Q : Config → Prop} {l₀ skip inspect : ℕ}
    (h₀ : decider.instr l₀ = read (reg 1) (l₀ + 1) (l₀ + 1) 103)
    (h₁ : decider.instr (l₀ + 1) = lt (reg 0) (const 1) inspect skip)
    (hskip : decider.CodeAt skip (skipClauseCode skip 1 l₀)) (st₀ : St)
    (hinsp : ∀ c ∈ φ, ∀ {p : ℕ}, LitsAt (encCNF φ) p c →
      ({ st₀ with p := p } : St).Bounded (bnd φ) → ∀ b : Bool,
      decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q
        (inspect, ({ st₀ with p := p } : St).regs b.toNat)) :
    ∀ (cs : CNF ℕ) {p : ℕ}, (∀ c ∈ cs, c ∈ φ) → ClausesAt (encCNF φ) p cs →
      ({ st₀ with p := p } : St).Bounded (bnd φ) → ∀ b : Bool,
      decider.AllBranches (encCNF φ) (bnd φ) (Post φ) Q
        (l₀, ({ st₀ with p := p } : St).regs b.toNat)
  | [], p, _, hcs, hB, b =>
    ab_of_reaches (reaches_read_p h₀ rfl hB (by simp only [hcs.getElem?_nil, readLabel]))
      (fun b => ab_reject hB b) b
  | c :: cs, p, hsub, hcs, hB, b => by
    obtain ⟨hc, hrest⟩ := hcs.cons
    refine ab_of_reaches (reaches_read_p h₀ rfl hB (readLabel_some _ _ _ hc.getElem?_isSome rfl))
      (fun b => ab_choice h₁ hB (hinsp c (hsub c List.mem_cons_self) hc hB) (fun b => ?_) b) b
    have := hc.le_length
    rw [length_clauseBits, ← Nat.add_assoc] at hrest
    exact ab_of_reaches (reaches_skip_clause_p hskip hc rfl hB)
      (fun b => ab_scanLoop h₀ h₁ hskip st₀ hinsp cs
        (fun c hc => hsub c (List.mem_cons_of_mem _ hc)) hrest (by st_bounded) b) b

/-- **Every branch looking for a clause of width zero or more than two**, from the clauses `cs`,
halts, accepting only when it finds one. -/
theorem ab_modeA : ∀ (cs : CNF ℕ) {p : ℕ} {st : St}, (∀ c ∈ cs, c ∈ φ) →
    ClausesAt (encCNF φ) p cs → st.p = p → st.Bounded (bnd φ) → ∀ b : Bool,
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ) (fun _ => False) (3, st.regs b.toNat) := by
  rintro cs p st hsub hcs rfl hB b
  refine ab_scanLoop (l₀ := 3) (skip := 5) (inspect := 10) rfl rfl codeAt_skipClause₅ st
    (fun c hcφ _ hc hB b => ?_) cs hsub hcs hB b
  obtain ⟨st', hB', hw⟩ := reaches_width hc rfl hB 0 (Nat.zero_le _)
  refine ab_of_reaches hw (fun b => ?_) b
  split_ifs with hwidth
  · refine ab_accept hB' b (notMem_TwoSAT_iff.mpr ?_)
    exact hwidth.elim (fun h => .inr (.inl (List.length_eq_zero_iff.mp h ▸ hcφ)))
      fun h => .inl ⟨c, hcφ, by omega⟩
  · exact ab_reject hB' b

/-! ### The walk -/

variable (φ) in
/-- The position `pos` holds an occurrence of the literal `(v, b)` of the formula. -/
def Occ (pos v : ℕ) (b : Bool) : Prop :=
  (∃ c ∈ φ, (v, b) ∈ c) ∧ InfixAt (encCNF φ) pos (literalBits v b)

variable (φ) in
/-- **The registers at the head of the walk**: the starting occurrence of a variable `x`, the
occurrence of the variable `v` of the current literal and its polarity, the number of steps
within the length of the input, and the paths found so far: from `x` to the current literal in
the first phase, and from `x` to `¬x` and from `¬x` to the current literal in the second. -/
def LoopInv (st : St) : Prop :=
  ∃ x b₀ v b₁, Occ φ st.o₀ x b₀ ∧ Occ φ st.cur v b₁ ∧ st.sgn ≤ 1 ∧
    st.len = (encCNF φ).length ∧ st.steps ≤ st.len ∧ st.Bounded (bnd φ) ∧
    ((st.phase = 0 ∧ Relation.ReflTransGen φ.Implies (x, true) (v, decide (st.sgn = 1))) ∨
      (st.phase = 1 ∧ Relation.ReflTransGen φ.Implies (x, true) (x, false) ∧
        Relation.ReflTransGen φ.Implies (x, false) (v, decide (st.sgn = 1))))

variable (φ) in
/-- The measure of the walk: the steps left, the first phase counting double. -/
def measure (st : St) : ℕ := (1 - st.phase) * ((encCNF φ).length + 1) + (st.len - st.steps)

theorem codeAt_skipClause₂₂ : decider.CodeAt 22 (skipClauseCode 22 1 20) :=
  codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_skipLit₂₉ : decider.CodeAt 29 (skipLitCode 29 1 27) := codeAt_of_prefix ⟨_, rfl⟩

/-- The chosen occurrence becomes the starting one and the current one, with polarity `1`. -/
theorem reaches_pick {p : ℕ} {st : St} (hp : st.p = p) (hB : st.Bounded (bnd φ)) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (32, st.regs 0)
      (35, ({ st with o₀ := p, cur := p, sgn := 1 } : St).regs 0) := by
  subst hp
  have := mem_regs_zero hB
  have := hB.1
  have := one_le_bnd (φ := φ)
  cp_step
  cp_step [List.getD_set_ne (by decide : 2 ≠ 1)]
  cp_step [St.set_regs_2, St.set_regs_3, St.set_regs_4]

private theorem reaches_lit₂₇ {m : Literal ℕ} {p : ℕ}
    (hm : InfixAt (encCNF φ) p (literalBits m.1 m.2)) {st : St} (hp : st.p = p)
    (hB : st.Bounded (bnd φ)) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (27, st.regs 0) (28, st.regs 0) ∧
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (29, st.regs 0)
      (27, ({ st with p := p + (literalBits m.1 m.2).length } : St).regs 0) := by
  have hend := le_bnd_of_infixAt hm (literalBits_ne_nil _ _)
  refine ⟨reaches_read_p (l' := 28) rfl hp hB (by simp only [hm.literal_start, readLabel]), ?_⟩
  simpa [St.set_regs_1] using reaches_skipLitCode codeAt_skipLit₂₉ (by omega) (by simp) hm
    (St.getD_regs_1 st 0 ▸ hp) (mem_regs_zero hB) hend

/-- **Every branch choosing the starting occurrence within a clause**, from its literals `ls`,
rejects or reaches the head of the walk. -/
theorem ab_startLit {c : Clause ℕ} (hcφ : c ∈ φ) : ∀ (ls : Clause ℕ) {p : ℕ} {st : St},
    (∀ l ∈ ls, l ∈ c) → LitsAt (encCNF φ) p ls → st.p = p → st.Bounded (bnd φ) →
    st.phase = 0 → st.steps = 0 → st.len = (encCNF φ).length → ∀ b : Bool,
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool), s = (35, st'.regs b'.toNat) ∧ LoopInv φ st')
      (27, st.regs b.toNat)
  | [], p, st, _, hls, hp, hB, _, _, _, b =>
    ab_of_reaches (reaches_read_p (show decider.instr 27 = _ from rfl) hp hB
      (by simp only [hls.getElem?_nil, readLabel])) (fun b => ab_reject hB b) b
  | m :: ls, p, st, hsub, hls, hp, hB, hph, hst, hlen, b => by
    obtain ⟨hm, hrest⟩ := hls.cons
    have hend := le_bnd_of_infixAt hm (literalBits_ne_nil _ _)
    obtain ⟨h₂₇, hskip⟩ := reaches_lit₂₇ hm hp hB
    refine ab_of_reaches h₂₇ (fun b => ab_choice rfl hB (fun b => ?_) (fun b => ?_) b) b
    · refine ab_of_reaches (reaches_pick hp hB) (fun b => .exit ⟨_, b, rfl, ?_⟩) b
      have hocc : Occ φ p m.1 m.2 := ⟨⟨c, hcφ, hsub m List.mem_cons_self⟩, hm⟩
      exact ⟨m.1, m.2, m.1, m.2, hocc, hocc, by simp, hlen, by simp [hst], by st_bounded,
        .inl ⟨hph, .refl⟩⟩
    · exact ab_of_reaches hskip (fun b => ab_startLit hcφ ls
        (st := { st with p := p + (literalBits m.1 m.2).length })
        (fun l hl => hsub l (List.mem_cons_of_mem _ hl)) hrest rfl (by st_bounded) hph hst hlen
        b) b

/-- **Every branch choosing the starting occurrence**, from the clauses `cs`, rejects or reaches
the head of the walk. -/
theorem ab_start : ∀ (cs : CNF ℕ) {p : ℕ} {st : St}, (∀ c ∈ cs, c ∈ φ) →
    ClausesAt (encCNF φ) p cs → st.p = p → st.Bounded (bnd φ) →
    st.phase = 0 → st.steps = 0 → st.len = (encCNF φ).length → ∀ b : Bool,
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool), s = (35, st'.regs b'.toNat) ∧ LoopInv φ st')
      (20, st.regs b.toNat) := by
  rintro cs p st hsub hcs rfl hB hph hst hlen b
  exact ab_scanLoop (l₀ := 20) (skip := 22) (inspect := 27) rfl rfl codeAt_skipClause₂₂ st
    (fun c hcφ _ hc hB b => ab_startLit hcφ c (fun _ h => h) hc rfl hB hph hst hlen b) cs hsub hcs
    hB b

theorem codeAt_cmpVar₇₉ : decider.CodeAt 79 (cmpVarCode 79 12 3 13 14 89 103) :=
  codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_sign₈₉ : decider.CodeAt 89 (signCode 89 12 15 93 94) := codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_sign₉₆ : decider.CodeAt 96 (signCode 96 11 15 100 101) := codeAt_of_prefix ⟨_, rfl⟩

/-- Checking at labels `93` and `94` whether the read polarity `b` is opposite to `st.sgn`. -/
private theorem reaches_check_polarity {st : St} (hsgn : st.sgn ≤ 1)
    (hB : st.Bounded (bnd φ)) (b : Bool) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ))
      (if b then 93 else 94, st.regs 0)
      (if b = !decide (st.sgn = 1) then 95 else 103, st.regs 0) := by
  have := mem_regs_zero hB
  cases b <;> rcases (by omega : st.sgn = 0 ∨ st.sgn = 1) with hs | hs <;> (
    cp_step [hs]
    simp [Reaches.refl])

/-- The register state after moving along a verified arc to literal `ℓ'` at `st.o₁`. -/
private def checkMoveSt (st : St) (ℓ' : Literal ℕ) : St :=
  { st with cur := st.o₁, t := st.o₁ + 8 * ℓ'.1.bits.length, sgn := ℓ'.2.toNat }

/-- Moving from label `95` to the new current literal `ℓ'` at `st.o₁` and returning to `35`. -/
private theorem reaches_check_move {st : St} {ℓ' : Literal ℕ}
    (ho₁ : InfixAt (encCNF φ) st.o₁ (literalBits ℓ'.1 ℓ'.2)) (hB : st.Bounded (bnd φ)) :
    (checkMoveSt st ℓ').Bounded (bnd φ) ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (95, st.regs 0)
        (35, (checkMoveSt st ℓ').regs 0) := by
  have hend₁ := le_bnd_of_infixAt ho₁ (literalBits_ne_nil _ _)
  have := length_literalBits ℓ'.1 ℓ'.2
  have := Bool.toNat_le ℓ'.2
  have hregs := mem_regs_zero hB
  refine ⟨by simp only [checkMoveSt]; st_bounded, ?_⟩
  cp_step
  refine (reaches_signCode codeAt_sign₉₆ (regs := (st.regs 0).set 3 st.o₁) (B := bnd φ)
    (by omega) (by omega) (by simp) ho₁
    ((List.getD_set_ne (by decide : 3 ≠ 11)).trans (St.getD_regs_11 st 0))
    (List.forall_mem_set_of_forall_mem hregs (by omega)) hend₁).trans ?_
  rcases hb : ℓ'.2 <;>
    cp_step [hb, Bool.toNat_false, Bool.toNat_true, St.set_regs_3, St.set_regs_15, St.set_regs_4,
      checkMoveSt]

/-- **Checking an arc and moving along it**, deterministically: from label `79`, with the
occurrences of literals `ℓ'` and `m` in registers `11` and `12`, the run moves to `ℓ'` at the
head of the walk when `m` is the negation of the current literal, and rejects otherwise. -/
theorem reaches_check {st : St} {v : ℕ} {b₁ : Bool}
    (hcur : InfixAt (encCNF φ) st.cur (literalBits v b₁)) (hsgn : st.sgn ≤ 1)
    {ℓ' m : Literal ℕ} (ho₁ : InfixAt (encCNF φ) st.o₁ (literalBits ℓ'.1 ℓ'.2))
    (ho₂ : InfixAt (encCNF φ) st.o₂ (literalBits m.1 m.2)) (hB : st.Bounded (bnd φ)) :
    ∃ st' : St, st'.Bounded (bnd φ) ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (79, st.regs 0)
        (if m = Std.Sat.Literal.negate (v, decide (st.sgn = 1)) then 35 else 103, st'.regs 0) ∧
      (m = Std.Sat.Literal.negate (v, decide (st.sgn = 1)) → st'.o₀ = st.o₀ ∧
        st'.phase = st.phase ∧ st'.steps = st.steps ∧ st'.len = st.len ∧ st'.cur = st.o₁ ∧
        st'.sgn = ℓ'.2.toNat) := by
  have hend₂ := le_bnd_of_infixAt ho₂ (literalBits_ne_nil _ _)
  have hendc := le_bnd_of_infixAt hcur (literalBits_ne_nil _ _)
  have := length_literalBits m.1 m.2
  obtain ⟨x, y, hx, hy, hcmp⟩ := reaches_cmpVarCode codeAt_cmpVar₇₉ (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by simp) (by simp) ho₂ hcur
    (St.getD_regs_12 st 0) (St.getD_regs_3 st 0) (mem_regs_zero hB) hend₂ hendc
  simp only [St.set_regs_13, St.set_regs_14] at hcmp
  set st₁ : St := { st with t₁ := x, t₂ := y }
  have hB₁ : st₁.Bounded (bnd φ) := by simp only [st₁]; st_bounded
  by_cases hmv : m.1 = v
  · rw [ite_eq_left hmv] at hcmp
    have hsign := reaches_signCode codeAt_sign₈₉ (B := bnd φ) (by omega) (by omega) (by simp) ho₂
      (St.getD_regs_12 st₁ 0) (mem_regs_zero hB₁) hend₂
    simp only [St.set_regs_15] at hsign
    set st₂ : St := { st₁ with t := st.o₂ + 8 * m.1.bits.length }
    have hB₂ : st₂.Bounded (bnd φ) := by simp only [st₂, st₁]; st_bounded
    have hneg : m = Std.Sat.Literal.negate (v, decide (st.sgn = 1)) ↔
        m.2 = !decide (st.sgn = 1) := by
      rcases m with ⟨_, mb⟩; subst hmv; simp [Std.Sat.Literal.negate]
    have hpol := hcmp.trans (hsign.trans (reaches_check_polarity (st := st₂) hsgn hB₂ m.2))
    by_cases hpass : m = Std.Sat.Literal.negate (v, decide (st.sgn = 1))
    · obtain ⟨hBmv, hmv'⟩ := reaches_check_move (st := st₂) ho₁ hB₂
      rw [ite_eq_left (hneg.mp hpass)] at hpol
      exact ⟨checkMoveSt st₂ ℓ', hBmv, by rw [ite_eq_left hpass]; exact hpol.trans hmv',
        fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · rw [ite_eq_right (mt hneg.mpr hpass)] at hpol
      exact ⟨st₂, hB₂, by simpa [hpass] using hpol, fun h => absurd h hpass⟩
  · have hne : m ≠ Std.Sat.Literal.negate (v, decide (st.sgn = 1)) := fun h => hmv (by rw [h]; rfl)
    exact ⟨st₁, hB₁, by simpa [hmv, hne] using hcmp, fun h => absurd h hne⟩

/-- **Every branch checking an arc and moving along it**: from label `79`, with the occurrences
of literals `ℓ'` and `m` of a clause `c` in registers `11` and `12`, every branch rejects or moves
to `ℓ'` when `m` is the negation of the current literal, in which case the arc exists. -/
theorem ab_check {st : St} {c : Clause ℕ} (hcφ : c ∈ φ) {v : ℕ} {b₁ : Bool}
    (hcur : InfixAt (encCNF φ) st.cur (literalBits v b₁)) (hsgn : st.sgn ≤ 1)
    {ℓ' m : Literal ℕ} (hℓ' : ℓ' ∈ c) (hm : m ∈ c) (hc : ∀ y ∈ c, y = m ∨ y = ℓ')
    (ho₁ : InfixAt (encCNF φ) st.o₁ (literalBits ℓ'.1 ℓ'.2))
    (ho₂ : InfixAt (encCNF φ) st.o₂ (literalBits m.1 m.2)) (hB : st.Bounded (bnd φ))
    (b : Bool) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool), s = (35, st'.regs b'.toNat) ∧ st'.o₀ = st.o₀ ∧
        st'.phase = st.phase ∧ st'.steps = st.steps ∧ st'.len = st.len ∧ st'.cur = st.o₁ ∧
        st'.sgn = ℓ'.2.toNat ∧ st'.Bounded (bnd φ) ∧
        φ.Implies (v, decide (st.sgn = 1)) ℓ')
      (79, st.regs b.toNat) := by
  obtain ⟨st', hB', hreach, hfields⟩ := reaches_check hcur hsgn ho₁ ho₂ hB
  refine ab_of_reaches hreach (fun b => ?_) b
  split_ifs with hneg
  · obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := hfields hneg
    refine .exit ⟨st', b, rfl, h₀, h₁, h₂, h₃, h₄, h₅, hB', c, hcφ, hneg ▸ hm, hℓ', fun y hy => ?_⟩
    rcases hc y hy with rfl | rfl <;> simp [hneg]
  · exact ab_reject hB' b

theorem codeAt_skipLit₆₃ : decider.CodeAt 63 (skipLitCode 63 9 66) := codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_skipLit₇₀ : decider.CodeAt 70 (skipLitCode 70 10 73) := codeAt_of_prefix ⟨_, rfl⟩

theorem codeAt_skipClause₅₅ : decider.CodeAt 55 (skipClauseCode 55 1 53) :=
  codeAt_of_prefix ⟨_, rfl⟩

variable (φ) in
/-- The registers at label `79`: the walk unchanged, and the occurrences of two literals `ℓ'` and
`m` of the clause `c` in registers `11` and `12`, such that `c` has no other literal. -/
def Ready (st st' : St) (c : Clause ℕ) : Prop :=
  st'.o₀ = st.o₀ ∧ st'.cur = st.cur ∧ st'.sgn = st.sgn ∧ st'.phase = st.phase ∧
    st'.steps = st.steps ∧ st'.len = st.len ∧ st'.Bounded (bnd φ) ∧
    ∃ ℓ' m : Literal ℕ, ℓ' ∈ c ∧ m ∈ c ∧ (∀ y ∈ c, y = m ∨ y = ℓ') ∧
      InfixAt (encCNF φ) st'.o₁ (literalBits ℓ'.1 ℓ'.2) ∧
      InfixAt (encCNF φ) st'.o₂ (literalBits m.1 m.2)

/-- The registers of the walk agree. -/
def Same (st st' : St) : Prop :=
  st'.o₀ = st.o₀ ∧ st'.cur = st.cur ∧ st'.sgn = st.sgn ∧ st'.phase = st.phase ∧
    st'.steps = st.steps ∧ st'.len = st.len

theorem Same.rfl' {st : St} : Same st st := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading the first literal `m₁` of a non-empty clause from label `60` to label `66`. -/
private theorem reaches_inspect_first {st : St} {m₁ : Literal ℕ}
    (hm₁ : InfixAt (encCNF φ) st.p (literalBits m₁.1 m₁.2)) (hB : st.Bounded (bnd φ)) :
    ({ st with q₁ := st.p, q₂ := st.p + (literalBits m₁.1 m₁.2).length } : St).Bounded (bnd φ) ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (60, st.regs 0)
        (66,
          ({ st with q₁ := st.p, q₂ := st.p + (literalBits m₁.1 m₁.2).length } : St).regs 0) := by
  have hend₁ := le_bnd_of_infixAt hm₁ (literalBits_ne_nil _ _)
  have hregs := mem_regs_zero hB
  have hp := hB.1
  refine ⟨by st_bounded, ?_⟩
  cp_step
  cp_step [List.getD_set_self (by simp : 8 < (st.regs 0).length), hm₁.literal_start]
  cp_step [List.getD_set_self (by simp : 8 < (st.regs 0).length)]
  simpa only [St.set_regs_8, St.set_regs_9] using reaches_skipLitCode codeAt_skipLit₆₃
    (regs := ((st.regs 0).set 8 st.p).set 9 st.p) (by omega) (by simp) hm₁
    (List.getD_set_self (by simp))
    (List.forall_mem_set_of_forall_mem (List.forall_mem_set_of_forall_mem hregs hp) hp) hend₁

/-- Reading the second literal `m₂` of a clause from label `66` and checking for a third. -/
private theorem reaches_inspect_second {st₂ : St} {m₂ : Literal ℕ} {rest : Clause ℕ}
    (hrest : LitsAt (encCNF φ) st₂.q₂ (m₂ :: rest)) (hB₂ : st₂.Bounded (bnd φ)) :
    ∃ st₃ : St, st₃.Bounded (bnd φ) ∧ Same st₂ st₃ ∧ st₃.q₁ = st₂.q₁ ∧ st₃.q₂ = st₂.q₂ ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (66, st₂.regs 0)
        (if rest = [] then 74 else 103, st₃.regs 0) := by
  obtain ⟨hm₂, hrest₂⟩ := hrest.cons
  have hend₂ := le_bnd_of_infixAt hm₂ (literalBits_ne_nil _ _)
  have hregs := mem_regs_zero hB₂
  set st₃ : St := { st₂ with q₃ := st₂.q₂ + (literalBits m₂.1 m₂.2).length }
  have hB₃ : st₃.Bounded (bnd φ) := by simp only [st₃]; st_bounded
  have h₇₃ : decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (66, st₂.regs 0)
      (73, st₃.regs 0) := by
    cp_step [hm₂.literal_start]
    cp_step
    simpa [st₃, St.set_regs_10] using reaches_skipLitCode codeAt_skipLit₇₀ (by omega) (by simp) hm₂
      (List.getD_set_self (by simp)) (List.forall_mem_set_of_forall_mem hregs (by omega)) hend₂
  refine ⟨st₃, hB₃, Same.rfl', rfl, rfl, h₇₃.trans ?_⟩
  have := mem_regs_zero hB₃
  rcases rest with _ | ⟨m₃, rest⟩ <;> simp only [reduceCtorEq, ↓reduceIte]
  · cp_step [st₃, hrest₂.getElem?_nil]
  · cp_step [st₃, hrest₂.cons.1.literal_start]

/-- **Reading a guessed clause**, deterministically, up to the guess of its literal `ℓ'`: an
empty clause or one with more than two literals is rejected, the literal of a unit clause is
taken, and the two literals of a clause of width two are placed in registers `8` and `9`. -/
theorem reaches_inspect {q : ℕ} {c : Clause ℕ} (hc : LitsAt (encCNF φ) q c) {st : St}
    (hp : st.p = q) (hB : st.Bounded (bnd φ)) :
    ∃ st' : St, st'.Bounded (bnd φ) ∧ Same st st' ∧
      ((c = [] ∨ 3 ≤ c.length) ∧
          decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (60, st.regs 0)
            (103, st'.regs 0) ∨
        (∃ m₁, c = [m₁] ∧ InfixAt (encCNF φ) st'.o₁ (literalBits m₁.1 m₁.2) ∧
          InfixAt (encCNF φ) st'.o₂ (literalBits m₁.1 m₁.2) ∧
          decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (60, st.regs 0)
            (79, st'.regs 0)) ∨
        (∃ m₁ m₂, c = [m₁, m₂] ∧ InfixAt (encCNF φ) st'.q₁ (literalBits m₁.1 m₁.2) ∧
          InfixAt (encCNF φ) st'.q₂ (literalBits m₂.1 m₂.2) ∧
          decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (60, st.regs 0)
            (74, st'.regs 0))) := by
  subst hp
  rcases c with _ | ⟨m₁, rest⟩
  · refine ⟨{ st with q₁ := st.p }, by st_bounded, Same.rfl', .inl ⟨.inl rfl, ?_⟩⟩
    have := mem_regs_zero hB
    have := hB.1
    cp_step
    cp_step [List.getD_set_self (by simp : 8 < (st.regs 0).length), hc.getElem?_nil,
      St.set_regs_8]
  obtain ⟨hm₁, hrest⟩ := hc.cons
  have hend₁ := le_bnd_of_infixAt hm₁ (literalBits_ne_nil _ _)
  set st₂ : St := { st with q₁ := st.p, q₂ := st.p + (literalBits m₁.1 m₁.2).length }
  obtain ⟨hB₂, h₆₆⟩ := reaches_inspect_first hm₁ hB
  rcases rest with _ | ⟨m₂, rest⟩
  · refine ⟨{ st₂ with o₁ := st.p, o₂ := st.p }, by dsimp only [st₂]; st_bounded, Same.rfl',
      .inr (.inl ⟨m₁, rfl, hm₁, hm₁, h₆₆.trans ?_⟩)⟩
    have := mem_regs_zero hB₂
    have := hB.1
    cp_step [st₂, hrest.getElem?_nil]
    cp_step [st₂]
    cp_step [List.getD_set_ne (by decide : 11 ≠ 8), st₂, St.set_regs_11, St.set_regs_12]
  obtain ⟨st₃, hB₃, hsame, hq₁, hq₂, h₂⟩ := reaches_inspect_second (st₂ := st₂) hrest hB₂
  rcases rest with _ | ⟨m₃, rest⟩
  · exact ⟨st₃, hB₃, hsame, .inr (.inr ⟨m₁, m₂, rfl, hq₁ ▸ hm₁, hq₂ ▸ hrest.cons.1, h₆₆.trans h₂⟩)⟩
  · exact ⟨st₃, hB₃, hsame, .inl ⟨.inr (by simp), h₆₆.trans h₂⟩⟩

/-- The registers after the guess of `ℓ'` in a clause of width two. -/
def pairSt (st : St) (first : Bool) : St :=
  { st with
    o₁ := if first then st.q₁ else st.q₂
    o₂ := if first then st.q₂ else st.q₁ }

private theorem pairSt_bounded {st : St} (hB : st.Bounded (bnd φ)) (first : Bool) :
    (pairSt st first).Bounded (bnd φ) := by
  cases first <;> simp only [pairSt, Bool.false_eq_true, ite_false, ite_true] <;> st_bounded

/-- The guess of `ℓ'` in a clause of width two: the first literal, or the second. -/
theorem reaches_pair {st : St} (hB : st.Bounded (bnd φ)) (first : Bool) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ))
      (if first then 75 else 77, st.regs 0)
      (79, (pairSt st first).regs 0) := by
  have := mem_regs_zero hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hB
  cases first <;> (
    simp only [pairSt, Bool.false_eq_true, ↓reduceIte]
    cp_step
    cp_step [List.getD_set_ne (by decide : 11 ≠ 9), List.getD_set_ne (by decide : 11 ≠ 8),
      St.set_regs_11, St.set_regs_12])

/-- **Every branch reading a guessed clause** rejects it when it is empty or has more than two
literals, and otherwise guesses its literal `ℓ'`, the other literal being `m`. -/
theorem ab_inspect {p : ℕ} {c : Clause ℕ} (hc : LitsAt (encCNF φ) p c) {st : St}
    (hp : st.p = p) (hB : st.Bounded (bnd φ)) (b : Bool) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool), s = (79, st'.regs b'.toNat) ∧ Ready φ st st' c)
      (60, st.regs b.toNat) := by
  obtain ⟨st', hB', ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩, hcase⟩ := reaches_inspect hc hp hB
  rcases hcase with ⟨-, h⟩ | ⟨m₁, rfl, ho₁, ho₂, h⟩ | ⟨m₁, m₂, rfl, hq₁, hq₂, h⟩
  · exact ab_of_reaches h (fun b => ab_reject hB' b) b
  · exact ab_of_reaches h (fun b => .exit ⟨st', b, rfl, h₀, h₁, h₂, h₃, h₄, h₅, hB', m₁, m₁,
      by simp, by simp, fun y hy => .inl (by simpa using hy), ho₁, ho₂⟩) b
  · refine ab_of_reaches h (fun b => ab_choice rfl hB' (fun b => ?_) (fun b => ?_) b) b
    · exact ab_of_reaches (reaches_pair hB' true) (fun b => .exit ⟨_, b, rfl, h₀, h₁, h₂, h₃,
        h₄, h₅, pairSt_bounded hB' true, m₁, m₂, by simp, by simp,
        fun y hy => by simpa [or_comm] using hy, hq₁, hq₂⟩) b
    · exact ab_of_reaches (reaches_pair hB' false) (fun b => .exit ⟨_, b, rfl, h₀, h₁, h₂, h₃,
        h₄, h₅, pairSt_bounded hB' false, m₂, m₁, by simp, by simp,
        fun y hy => by simpa using hy, hq₂, hq₁⟩) b

/-- **Every branch guessing a clause**, from the clauses `cs`, rejects or reaches label `79` ready
to check one of them. -/
theorem ab_scan : ∀ (cs : CNF ℕ) {p : ℕ} {st : St}, (∀ c ∈ cs, c ∈ φ) →
    ClausesAt (encCNF φ) p cs → st.p = p → st.Bounded (bnd φ) → ∀ b : Bool,
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool) (c : Clause ℕ), c ∈ φ ∧ s = (79, st'.regs b'.toNat) ∧
        Ready φ st st' c)
      (53, st.regs b.toNat) := by
  rintro cs p st hsub hcs rfl hB b
  exact ab_scanLoop (l₀ := 53) (skip := 55) (inspect := 60) rfl rfl codeAt_skipClause₅₅ st
    (fun c hcφ _ hc hB b => (ab_inspect hc rfl hB b).mono
      fun _ ⟨st', b', hs, hr⟩ => ⟨st', b', c, hcφ, hs, hr⟩) cs hsub hcs hB b

theorem decide_toNat_eq_one (b : Bool) : decide (b.toNat = 1) = b := by
  cases b <;> rfl

/-- The registers after the test of the number of steps. -/
def stepSt (st : St) : St := { st with steps := st.steps + 1, p := 0 }

/-- **The test of the number of steps**, deterministically: from label `50`, the run continues
to guess a clause when fewer steps than the length of the input were taken. -/
theorem reaches_steps {st : St} (hB : st.Bounded (bnd φ)) (hlen : st.len = (encCNF φ).length)
    (hs : st.steps < st.len) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (50, st.regs 0)
      (53, (stepSt st).regs 0) := by
  have := mem_regs_zero hB
  have : st.steps + 1 ≤ bnd φ := by simp only [bnd]; omega
  cp_step
  cp_step
  cp_step [St.set_regs_6, St.set_regs_1, stepSt]

theorem stepSt_bounded {st : St} (hB : st.Bounded (bnd φ)) (hlen : st.len = (encCNF φ).length)
    (hs : st.steps < st.len) : (stepSt st).Bounded (bnd φ) := by
  simp only [stepSt]
  st_bounded

/-- **Every branch of a step of the walk**: from label `50`, every branch rejects or comes back
to the head of the walk one step further along an arc. -/
theorem ab_walk {st : St} (hinv : LoopInv φ st) (b : Bool) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool), s = (35, st'.regs b'.toNat) ∧ LoopInv φ st' ∧
        measure φ st' < measure φ st)
      (50, st.regs b.toNat) := by
  obtain ⟨x, b₀, v, b₁, hO₀, hOc, hsgn, hlen, hsteps, hB, hreach⟩ := hinv
  by_cases hs : st.steps < st.len
  · refine ab_of_reaches (reaches_steps hB hlen hs) (fun b => ?_) b
    refine (ab_scan φ (fun _ h => h) (clausesAt_encCNF φ) rfl (stepSt_bounded hB hlen hs) b).bind
      fun s ⟨st₂, b₂, c, hcφ, hs₂, hready⟩ => ?_
    subst hs₂
    obtain ⟨ho₀, hcur, hsg, hph, hst, hln, hB₂, ℓ', m, hℓ', hm, hc, ho₁, ho₂⟩ := hready
    refine (ab_check hcφ (hcur ▸ hOc.2) (hsg ▸ hsgn) hℓ' hm hc ho₁ ho₂ hB₂ b₂).mono
      fun s ⟨st₃, b₃, hs₃, h₀, hph', hst', hln', hcur₃, hsg₃, hB₃, harc⟩ => ⟨st₃, b₃, hs₃, ?_, ?_⟩
    · refine ⟨x, b₀, ℓ'.1, ℓ'.2, (h₀.trans ho₀) ▸ hO₀, ⟨⟨c, hcφ, hℓ'⟩, hcur₃ ▸ ho₁⟩,
        hsg₃ ▸ Bool.toNat_le _, hln'.trans (hln.trans hlen),
        by simp only [hst', hst, hln', hln, stepSt] at hsteps ⊢; omega, hB₃, ?_⟩
      rw [hph', hph, hsg₃, decide_toNat_eq_one]
      rcases hreach with ⟨h0, hr⟩ | ⟨h1, hr₁, hr₂⟩
      · exact .inl ⟨h0, hr.tail (hsg ▸ harc)⟩
      · exact .inr ⟨h1, hr₁, hr₂.tail (hsg ▸ harc)⟩
    · simp only [measure, hph', hph, hst', hst, hln', hln, stepSt]; omega
  · refine ab_of_reaches (x := 0) ?_ (fun b => ab_reject hB b) b
    have := mem_regs_zero hB
    cp_step

theorem codeAt_cmpVar₃₅ : decider.CodeAt 35 (cmpVarCode 35 3 2 13 14 45 50) :=
  codeAt_of_prefix ⟨_, rfl⟩

/-- The invariant does not depend on the cursors. -/
theorem LoopInv.cursors {st : St} (h : LoopInv φ st) {x y : ℕ} (hx : x ≤ bnd φ)
    (hy : y ≤ bnd φ) : LoopInv φ { st with t₁ := x, t₂ := y } := by
  obtain ⟨a, b₀, v, b₁, h₀, h₁, h₂, h₃, h₄, hB, h₅⟩ := h
  exact ⟨a, b₀, v, b₁, h₀, h₁, h₂, h₃, h₄, by st_bounded, h₅⟩

/-- Where the head of the walk goes: when the current literal is the end of the half, the walk
switches to the second half, or accepts at the end of the second; otherwise it continues. -/
def headOut (st : St) (same : Prop) [Decidable same] (X Y : ℕ) : ℕ × St :=
  if same ∧ st.sgn = st.phase then
    if st.phase = 0 then (50, { st with t₁ := X, t₂ := Y, phase := 1, steps := 0 })
    else (102, { st with t₁ := X, t₂ := Y })
  else (50, { st with t₁ := X, t₂ := Y })

/-- Comparing the polarity `st.sgn` with `st.phase` at label `45` when `v = x`. -/
private theorem reaches_head_eq {st : St} (hsgn : st.sgn ≤ 1) (hph : st.phase ≤ 1)
    (hB : st.Bounded (bnd φ)) {X Y : ℕ} (hX : X ≤ bnd φ) (hY : Y ≤ bnd φ) :
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ))
      (45, ({ st with t₁ := X, t₂ := Y } : St).regs 0)
      ((headOut st True X Y).1, (headOut st True X Y).2.regs 0) := by
  set st₁ : St := { st with t₁ := X, t₂ := Y }
  have hB₁ : st₁.Bounded (bnd φ) := by simp only [st₁]; st_bounded
  have := mem_regs_zero hB₁
  have := one_le_bnd (φ := φ)
  simp only [headOut, true_and]
  rcases (by omega : st.sgn = 0 ∨ st.sgn = 1) with hs | hs <;>
    rcases (by omega : st.phase = 0 ∨ st.phase = 1) with hp | hp <;>
    simp only [hs, hp, ↓reduceIte, zero_ne_one, one_ne_zero]
  · cp_step [show st₁.sgn = 0 from hs]
    cp_step [show st₁.phase = 0 from hp]
    cp_step
    cp_step [St.set_regs_5, St.set_regs_6, st₁, hs]
  all_goals
    cp_step [show st₁.sgn = _ from hs]
    cp_step [show st₁.phase = _ from hp]
    simp [st₁, hs, hp, Reaches.refl]

/-- **The head of the walk**, deterministically: it compares the current variable `v` with the
starting variable `x`, and the polarity with the phase. -/
theorem reaches_head {st : St} {x v : ℕ} {b₀ b₁ : Bool}
    (hO₀ : InfixAt (encCNF φ) st.o₀ (literalBits x b₀))
    (hOc : InfixAt (encCNF φ) st.cur (literalBits v b₁)) (hsgn : st.sgn ≤ 1)
    (hph : st.phase ≤ 1) (hB : st.Bounded (bnd φ)) :
    ∃ X Y, X ≤ bnd φ ∧ Y ≤ bnd φ ∧
      decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (35, st.regs 0)
        ((headOut st (v = x) X Y).1, (headOut st (v = x) X Y).2.regs 0) := by
  have hend₀ := le_bnd_of_infixAt hO₀ (literalBits_ne_nil _ _)
  have hendc := le_bnd_of_infixAt hOc (literalBits_ne_nil _ _)
  obtain ⟨X, Y, hX, hY, hcmp⟩ := reaches_cmpVarCode codeAt_cmpVar₃₅ (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by simp) (by simp) hOc hO₀
    (St.getD_regs_3 st 0) (St.getD_regs_2 st 0) (mem_regs_zero hB) hendc hend₀
  simp only [St.set_regs_13, St.set_regs_14] at hcmp
  refine ⟨X, Y, hX, hY, hcmp.trans ?_⟩
  by_cases hvx : v = x
  · simpa [headOut, hvx] using reaches_head_eq hsgn hph hB hX hY
  · simp only [headOut, hvx, false_and, ↓reduceIte]; exact Reaches.refl _

/-- **Every branch from the head of the walk** halts, accepting only when both paths are found,
or comes back to it with a smaller measure. -/
theorem ab_head {st : St} (hinv : LoopInv φ st) (b : Bool) :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ)
      (fun s => ∃ (st' : St) (b' : Bool), s = (35, st'.regs b'.toNat) ∧ LoopInv φ st' ∧
        measure φ st' < measure φ st)
      (35, st.regs b.toNat) := by
  obtain ⟨x, b₀, v, b₁, hO₀, hOc, hsgn, hlen, hsteps, hB, hreach⟩ := id hinv
  have hph : st.phase = 0 ∨ st.phase = 1 := by rcases hreach with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨X, Y, hX, hY, hhead⟩ := reaches_head hO₀.2 hOc.2 hsgn (by omega) hB
  refine ab_of_reaches hhead (fun b => ?_) b
  simp only [headOut]
  split_ifs with hhit hp0
  · obtain ⟨rfl, hsp⟩ := hhit
    obtain ⟨-, hr⟩ := hreach.resolve_right fun h => by omega
    refine (ab_walk (st := { st with t₁ := X, t₂ := Y, phase := 1, steps := 0 })
      ⟨v, b₀, v, b₁, hO₀, hOc, hsgn, hlen, by simp, by st_bounded,
        .inr ⟨rfl, by simpa [hsp, hp0] using hr, by simpa [hsp, hp0] using .refl⟩⟩
      b).mono fun _ ⟨st'', b', hs, hi, hm⟩ =>
      ⟨st'', b', hs, hi, by simp only [measure, hp0, hlen] at hm ⊢; omega⟩
  · obtain ⟨rfl, hsp⟩ := hhit
    obtain ⟨h1, hr₁, hr₂⟩ := hreach.resolve_left fun h => hp0 h.1
    exact ab_accept (by st_bounded) b
      (notMem_TwoSAT_iff.mpr (.inr (.inr ⟨v, hr₁, by simpa [hsp, h1] using hr₂⟩)))
  · exact ab_walk (hinv.cursors hX hY) b

/-- **Every branch from the head of the walk halts**, accepting only when both paths are
found. -/
theorem ab_loop : ∀ (n : ℕ) (st : St), measure φ st = n → LoopInv φ st → ∀ b : Bool,
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ) (fun _ => False) (35, st.regs b.toNat) := by
  intro n
  induction n using Nat.strong_induction_on with | _ n ih =>
  rintro st rfl hinv b
  exact (ab_head hinv b).bind fun _ ⟨st', b', hs, hinv', hm⟩ => hs ▸ ih _ hm st' rfl hinv' b'

/-! ### Every branch from the start -/

/-- The input is counted into register `7`. -/
theorem reaches_count : ∀ j ≤ (encCNF φ).length,
    decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (0, ({ len := j } : St).regs 0)
      (2, ({ len := (encCNF φ).length } : St).regs 0) := by
  intro j hj
  induction h : (encCNF φ).length - j generalizing j with
  | zero =>
    obtain rfl : j = (encCNF φ).length := by omega
    have := mem_regs_zero (φ := φ) (st := { len := (encCNF φ).length }) (by st_bounded)
    cp_step [List.getElem?_eq_none le_rfl]
  | succ m ih =>
    obtain ⟨_ | _, hb⟩ : ∃ b, (encCNF φ)[j]? = some b :=
      ⟨_, List.getElem?_eq_getElem (l := encCNF φ) (by omega)⟩
    all_goals
      have := mem_regs_zero (φ := φ) (st := { len := j }) (by st_bounded)
      have : j + 1 ≤ bnd φ := by simp only [bnd]; omega
      cp_step [hb]
      cp_step [St.set_regs_7]
      exact ih (j + 1) (by omega) (by omega)

theorem init_decider : decider.init = (0, ({} : St).regs 0) := rfl

/-- **Every branch of the decider halts, accepting only formulas outside `TwoSAT`**, with
registers at most the length of the input plus one. -/
theorem allBranches_decider :
    decider.AllBranches (encCNF φ) (bnd φ) (Post φ) (fun _ => False) decider.init := by
  have hB : ({ len := (encCNF φ).length } : St).Bounded (bnd φ) := by st_bounded
  rw [init_decider]
  simpa using ab_of_reaches (reaches_count (φ := φ) 0 (Nat.zero_le _))
    (fun b => ab_choice (show decider.instr 2 = _ from rfl) hB
      (fun b => ab_modeA φ (fun _ h => h) (clausesAt_encCNF φ) rfl hB b)
      (fun b => (ab_start φ (fun _ h => h) (clausesAt_encCNF φ) rfl hB rfl rfl rfl b).bind
        fun _ ⟨st', b', hs, hinv⟩ => hs ▸ ab_loop _ st' rfl hinv b') b) false

/-! ### An accepting branch -/

/-- One branch through deterministic code, with any choices before and after. -/
theorem branches_of_reaches' {l l' : ℕ} {st st' : St} {x : ℕ}
    (h : decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (l, st.regs x) (l', st'.regs x))
    (hne : l ≠ l') (b b' : Bool) :
    Branches (P := decider) (w := encCNF φ) (l, st.regs b.toNat) (l', st'.regs b'.toNat) := by
  simpa using branches_of_oblivious h b b' (fun h => absurd (congrArg Prod.fst h) hne)

/-- One step at a choice, taking the choice `b`. -/
theorem branches_choice {l yes no : ℕ} (hl : decider.instr l = lt (reg 0) (const 1) yes no)
    (st : St) (b b' : Bool) :
    Branches (P := decider) (w := encCNF φ) (l, st.regs b.toNat)
      (if b then no else yes, st.regs b'.toNat) := by
  have := Branches.single (P := decider) (w := encCNF φ) (s := (l, st.regs b.toNat))
    (by simp [halted, hl, Instr.halts]) b'
  rw [step_lt _ _ hl, withChoice_regs] at this
  simp only [eval_reg, St.getD_regs_0, eval_const] at this
  cases b <;> simpa using this

/-- **A branch guessing a clause** of a scanning loop: the code at `l₀` reads the scanning
position, the choice at `l₀ + 1` inspects the clause at `inspect` or skips it with the code at
`skip`. -/
theorem branches_scan {l₀ skip inspect : ℕ}
    (h₀ : decider.instr l₀ = read (reg 1) (l₀ + 1) (l₀ + 1) 103)
    (h₁ : decider.instr (l₀ + 1) = lt (reg 0) (const 1) inspect skip)
    (hskip : decider.CodeAt skip (skipClauseCode skip 1 l₀)) (hne : l₀ ≠ l₀ + 1)
    (hsk : skip ≠ l₀) :
    ∀ (cs : CNF ℕ) {p : ℕ} {st : St}, ClausesAt (encCNF φ) p cs → st.p = p →
      st.Bounded (bnd φ) → ∀ (i : ℕ) (hi : i < cs.length), ∀ b b' : Bool, ∃ q : ℕ,
        LitsAt (encCNF φ) q cs[i] ∧ q ≤ bnd φ ∧
        Branches (P := decider) (w := encCNF φ) (l₀, st.regs b.toNat)
          (inspect, ({ st with p := q } : St).regs b'.toNat)
  | [], _, _, _, _, _, i, hi, _, _ => absurd hi (by simp)
  | c :: cs, p, st, hcs, hp, hB, i, hi, b, b' => by
    obtain ⟨hc, hrest⟩ := hcs.cons
    have hread := reaches_read_p h₀ hp hB (readLabel_some _ _ 103 hc.getElem?_isSome rfl)
    rcases i with _ | i
    · exact ⟨p, hc, hp ▸ hB.1, (branches_of_reaches' hread hne b false).trans
        (by simpa [← hp] using branches_choice (φ := φ) h₁ st false b')⟩
    · have hl := hc.le_length
      rw [length_clauseBits, ← Nat.add_assoc] at hrest
      obtain ⟨q, hq, hqB, hbr⟩ := branches_scan h₀ h₁ hskip hne hsk cs
        (st := { st with p := p + (List.flatMap (fun l => literalBits l.1 l.2) c).length + 1 })
        hrest rfl (by st_bounded) i (by simpa using hi) false b'
      exact ⟨q, hq, hqB, (branches_of_reaches' hread hne b true).trans
        ((branches_choice (φ := φ) h₁ st true false).trans
          ((branches_of_reaches' (reaches_skip_clause_p hskip hc hp hB) hsk false false).trans
            (by simpa using hbr)))⟩

/-- **A branch guessing a literal** of a clause, at label `27`. -/
theorem branches_lit : ∀ (ls : Clause ℕ) {p : ℕ} {st : St}, LitsAt (encCNF φ) p ls → st.p = p →
    st.Bounded (bnd φ) → ∀ (j : ℕ) (hj : j < ls.length), ∀ b b' : Bool, ∃ q : ℕ,
      InfixAt (encCNF φ) q (literalBits ls[j].1 ls[j].2) ∧
      Branches (P := decider) (w := encCNF φ) (27, st.regs b.toNat)
        (32, ({ st with p := q } : St).regs b'.toNat)
  | [], _, _, _, _, _, j, hj, _, _ => absurd hj (by simp)
  | m :: ls, p, st, hls, hp, hB, j, hj, b, b' => by
    obtain ⟨hm, hrest⟩ := hls.cons
    have hend := le_bnd_of_infixAt hm (literalBits_ne_nil _ _)
    obtain ⟨hread, hskip⟩ := reaches_lit₂₇ hm hp hB
    rcases j with _ | j
    · exact ⟨p, hm, (branches_of_reaches' hread (by omega) b false).trans
        (by simpa [← hp] using branches_choice (φ := φ) (l := 28) rfl st false b')⟩
    · obtain ⟨q, hq, hbr⟩ := branches_lit ls hrest
        (st := { st with p := p + (literalBits m.1 m.2).length }) rfl (by st_bounded) j
        (by simpa using hj) false b'
      exact ⟨q, hq, (branches_of_reaches' hread (by omega) b true).trans
        ((branches_choice (φ := φ) (l := 28) rfl st true false).trans
          ((branches_of_reaches' hskip (by omega) false false).trans (by simpa using hbr)))⟩

private theorem branches_to_scan {b : Bool} :
    Branches (P := decider) (w := encCNF φ) decider.init
      (if b then 20 else 3, ({ len := (encCNF φ).length } : St).regs 0) := by
  rw [init_decider]
  exact (branches_of_reaches' (reaches_count 0 (Nat.zero_le _)) (by omega) false b).trans
    (branches_choice (show decider.instr 2 = _ from rfl) _ b false)

/-- **An accepting branch for a clause of width zero or more than two.** -/
theorem branches_modeA {c : Clause ℕ} (hc : c ∈ φ) (hw : c.length = 0 ∨ 3 ≤ c.length) :
    ∃ s, Branches (P := decider) (w := encCNF φ) decider.init s ∧
      decider.instr s.1 = .accept := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hB : ({ len := (encCNF φ).length } : St).Bounded (bnd φ) := by st_bounded
  obtain ⟨q, hq, hqB, hscan⟩ := branches_scan (φ := φ) (l₀ := 3) (skip := 5) (inspect := 10) rfl
    rfl codeAt_skipClause₅ (by omega) (by omega) φ (clausesAt_encCNF φ) rfl hB i hi false false
  obtain ⟨st', -, hwidth⟩ := reaches_width hq
    (st := { ({ len := (encCNF φ).length } : St) with p := q }) rfl (by st_bounded) 0
    (Nat.zero_le _)
  rw [ite_eq_left hw] at hwidth
  exact ⟨(102, st'.regs 0), (branches_to_scan (b := false)).trans
    (hscan.trans (branches_of_reaches' hwidth (by omega) false false)), rfl⟩

/-- Two literals `ℓ'` and `m` covering a two-literal clause `[m₁, m₂]` match in one of the two
orders. -/
private theorem pair_choice {ℓ' m m₁ m₂ : Literal ℕ} (hm : m ∈ [m₁, m₂]) (hℓ' : ℓ' ∈ [m₁, m₂])
    (hall : ∀ y ∈ [m₁, m₂], y = m ∨ y = ℓ') :
    (ℓ' = m₁ ∧ m = m₂) ∨ (ℓ' = m₂ ∧ m = m₁) := by
  have := hall m₁ (.head _)
  have := hall m₂ (.tail _ (.head _))
  grind

/-- Choosing the order of the two literals of a binary clause at label `74` so that `ℓ'` is in
`o₁` and `m` is in `o₂`. -/
private theorem branches_arc_pair {st st₂ st₃ : St} {b : Bool} {ℓ' m m₁ m₂ : Literal ℕ}
    (hB₃ : st₃.Bounded (bnd φ)) (hsame : Same st₂ st₃)
    (hm : m ∈ [m₁, m₂]) (hℓ' : ℓ' ∈ [m₁, m₂]) (hall : ∀ y ∈ [m₁, m₂], y = m ∨ y = ℓ')
    (hq₁ : InfixAt (encCNF φ) st₃.q₁ (literalBits m₁.1 m₁.2))
    (hq₂ : InfixAt (encCNF φ) st₃.q₂ (literalBits m₂.1 m₂.2))
    (hto60 : Branches (P := decider) (w := encCNF φ) (50, st.regs b.toNat)
      (60, st₂.regs (false : Bool).toNat))
    (h : decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (60, st₂.regs 0)
      (74, st₃.regs 0)) :
    ∃ st₄ : St, st₄.Bounded (bnd φ) ∧ Same st₂ st₄ ∧
      InfixAt (encCNF φ) st₄.o₁ (literalBits ℓ'.1 ℓ'.2) ∧
      InfixAt (encCNF φ) st₄.o₂ (literalBits m.1 m.2) ∧
      Branches (P := decider) (w := encCNF φ) (50, st.regs b.toNat)
        (79, st₄.regs (false : Bool).toNat) := by
  have hgo (first : Bool) : Branches (P := decider) (w := encCNF φ) (50, st.regs b.toNat)
      (79, (pairSt st₃ first).regs (false : Bool).toNat) := by
    have hch : Branches (P := decider) (w := encCNF φ) (74, st₃.regs (!first).toNat)
        (if first then 75 else 77, st₃.regs 0) := by
      cases first <;> exact branches_choice (φ := φ) (l := 74) rfl st₃ _ false
    exact hto60.trans ((branches_of_reaches' h (by omega) false (!first)).trans
      (hch.trans (branches_of_reaches' (reaches_pair hB₃ first) (by cases first <;> simp)
        false false)))
  rcases pair_choice hm hℓ' hall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, pairSt_bounded hB₃ true, hsame, hq₁, hq₂, hgo true⟩
  · exact ⟨_, pairSt_bounded hB₃ false, hsame, hq₂, hq₁, hgo false⟩

/-- **A branch along an arc** of the implication graph, from label `50` back to the head of the
walk, for a formula whose clauses have one or two literals. -/
theorem branches_arc {st : St} {v : ℕ} {b₁ : Bool}
    (hcur : InfixAt (encCNF φ) st.cur (literalBits v b₁)) (hsgn : st.sgn ≤ 1)
    (hB : st.Bounded (bnd φ)) (hlen : st.len = (encCNF φ).length) (hs : st.steps < st.len)
    (hw : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 2) {ℓ' : Literal ℕ}
    (harc : φ.Implies (v, decide (st.sgn = 1)) ℓ') (b : Bool) :
    ∃ (st' : St) (b' : Bool), Branches (P := decider) (w := encCNF φ) (50, st.regs b.toNat)
      (35, st'.regs b'.toNat) ∧ st'.o₀ = st.o₀ ∧ st'.phase = st.phase ∧
      st'.steps = st.steps + 1 ∧ st'.len = st.len ∧ Occ φ st'.cur ℓ'.1 ℓ'.2 ∧
      st'.sgn = ℓ'.2.toNat ∧ st'.Bounded (bnd φ) := by
  obtain ⟨c, hcφ, hneg, hℓ', hall⟩ := harc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcφ
  have hB₁ := stepSt_bounded hB hlen hs
  obtain ⟨q, hq, hqB, hscan⟩ := branches_scan (φ := φ) (l₀ := 53) (skip := 55) (inspect := 60)
    rfl rfl codeAt_skipClause₅₅ (by omega) (by omega) φ (clausesAt_encCNF φ) rfl hB₁ i hi false
    false
  set st₂ : St := { stepSt st with p := q }
  have hB₂ : st₂.Bounded (bnd φ) := by simp only [st₂, stepSt]; st_bounded
  have hto60 := (branches_of_reaches' (reaches_steps hB hlen hs) (by omega) b false).trans hscan
  obtain ⟨st₃, hB₃, hsame, hcase⟩ := reaches_inspect hq rfl hB₂
  obtain ⟨st₄, hB₄, ⟨h₄₀, h₄₁, h₄₂, h₄₃, h₄₄, h₄₅⟩, ho₁, ho₂, hto79⟩ :
      ∃ st₄ : St, st₄.Bounded (bnd φ) ∧ Same st₂ st₄ ∧
        InfixAt (encCNF φ) st₄.o₁ (literalBits ℓ'.1 ℓ'.2) ∧
        InfixAt (encCNF φ) st₄.o₂ (literalBits (Std.Sat.Literal.negate (v, decide (st.sgn = 1))).1
          (Std.Sat.Literal.negate (v, decide (st.sgn = 1))).2) ∧
        Branches (P := decider) (w := encCNF φ) (50, st.regs b.toNat)
          (79, st₄.regs (false : Bool).toNat) := by
    rcases hcase with ⟨hbad, -⟩ | ⟨m₁, hc, ho₁, ho₂, h⟩ | ⟨m₁, m₂, hc, hq₁, hq₂, h⟩
    · have := hw _ hcφ; rcases hbad with h | h <;> [simp [h] at this; omega]
    · rw [hc] at hneg hℓ'; simp only [List.mem_singleton] at hneg hℓ'
      exact ⟨st₃, hB₃, hsame, hℓ' ▸ ho₁, hneg ▸ ho₂,
        hto60.trans (branches_of_reaches' h (by omega) false false)⟩
    · rw [hc] at hneg hℓ' hall; exact branches_arc_pair hB₃ hsame hneg hℓ' hall hq₁ hq₂ hto60 h
  obtain ⟨st₅, hB₅, hcheck, hfields⟩ := reaches_check (h₄₁ ▸ hcur) (by rw [h₄₂]; exact hsgn)
    ho₁ ho₂ hB₄
  have hpass : Std.Sat.Literal.negate (v, decide (st.sgn = 1)) =
      Std.Sat.Literal.negate (v, decide (st₄.sgn = 1)) := by simp [h₄₂, st₂, stepSt]
  rw [ite_eq_left hpass] at hcheck
  obtain ⟨h₅₀, h₅₁, h₅₂, h₅₃, h₅₄, h₅₅⟩ := hfields hpass
  refine ⟨st₅, false, hto79.trans (branches_of_reaches' hcheck (by omega) false false),
    h₅₀.trans h₄₀, h₅₁.trans h₄₃, h₅₂.trans h₄₄, h₅₃.trans h₄₅, ⟨⟨_, hcφ, hℓ'⟩, h₅₄ ▸ ho₁⟩, h₅₅,
    hB₅⟩

/-- Reaching the target of the current half of the walk at label `35`: phase `0` switches to phase
`1` at label `50`, and phase `1` accepts at label `102`. -/
private theorem branches_walk_hit {st : St} {x : ℕ} {b₁ : Bool}
    (hOc : InfixAt (encCNF φ) st.cur (literalBits x b₁)) (hB : st.Bounded (bnd φ))
    {X Y : ℕ} (hX : X ≤ bnd φ) (hY : Y ≤ bnd φ)
    (hhead : decider.Reaches (encCNF φ) (decider.Oblivious (bnd φ)) (35, st.regs 0)
      ((headOut st True X Y).1, (headOut st True X Y).2.regs 0))
    (hhit : st.sgn = st.phase) (b : Bool) :
    ∃ (l : ℕ) (st' : St) (b' : Bool),
      Branches (P := decider) (w := encCNF φ) (35, st.regs b.toNat) (l, st'.regs b'.toNat) ∧
      (st.phase = 0 → l = 50 ∧ st'.phase = 1 ∧ st'.steps = 0 ∧ st'.o₀ = st.o₀ ∧
        st'.len = st.len ∧ st'.Bounded (bnd φ) ∧ st'.sgn = 0 ∧
        ∃ b₂, InfixAt (encCNF φ) st'.cur (literalBits x b₂)) ∧
      (st.phase = 1 → l = 102) := by
  simp only [headOut, true_and, hhit, ↓reduceIte] at hhead
  by_cases hp0 : st.phase = 0
  · rw [ite_eq_left hp0] at hhead
    exact ⟨50, _, false, branches_of_reaches' hhead (by omega) b false,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, by st_bounded, by simp [hp0], b₁, hOc⟩,
      fun h => absurd h (by omega)⟩
  · rw [ite_eq_right hp0] at hhead
    exact ⟨102, _, false, branches_of_reaches' hhead (by omega) b false,
      fun h => absurd h hp0, fun _ => rfl⟩

/-- **A branch along a walk** of the implication graph from the current literal to the end of the
half, within the remaining steps: it ends switching to the second half, or accepting at the end
of the second. -/
private theorem branches_walk (hw : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 2) {x : ℕ} {b₀ : Bool} :
    ∀ (m : ℕ) (st : St) {v : ℕ} {b₁ : Bool},
    InfixAt (encCNF φ) st.o₀ (literalBits x b₀) → InfixAt (encCNF φ) st.cur (literalBits v b₁) →
    st.sgn ≤ 1 → st.phase ≤ 1 → st.Bounded (bnd φ) → st.len = (encCNF φ).length →
    st.steps + m ≤ st.len →
    Relation.RelatesInSteps φ.Implies (v, decide (st.sgn = 1)) (x, decide (st.phase = 1)) m →
    ∀ b : Bool, ∃ (l : ℕ) (st' : St) (b' : Bool),
      Branches (P := decider) (w := encCNF φ) (35, st.regs b.toNat) (l, st'.regs b'.toNat) ∧
      (st.phase = 0 → l = 50 ∧ st'.phase = 1 ∧ st'.steps = 0 ∧ st'.o₀ = st.o₀ ∧
        st'.len = st.len ∧ st'.Bounded (bnd φ) ∧ st'.sgn = 0 ∧
        ∃ b₂, InfixAt (encCNF φ) st'.cur (literalBits x b₂)) ∧
      (st.phase = 1 → l = 102) := by
  intro m
  induction m with
  | zero =>
    intro st v b₁ hO₀ hOc hsgn hph hB hlen hsteps hpath b
    obtain ⟨rfl, hsp⟩ := Prod.mk.inj (Relation.RelatesInSteps.zero hpath)
    have hhit : st.sgn = st.phase := by grind
    obtain ⟨X, Y, hX, hY, hhead⟩ := reaches_head hO₀ hOc hsgn hph hB
    exact branches_walk_hit hOc hB hX hY (by simpa [headOut] using hhead) hhit b
  | succ m ih =>
    intro st v b₁ hO₀ hOc hsgn hph hB hlen hsteps hpath b
    obtain ⟨ℓ₁, harc, hrest⟩ := hpath.succ'
    obtain ⟨X, Y, hX, hY, hhead⟩ := reaches_head hO₀ hOc hsgn hph hB
    by_cases hhit : v = x ∧ st.sgn = st.phase
    · exact branches_walk_hit (hhit.1 ▸ hOc) hB hX hY (by simpa [headOut, hhit.1] using hhead)
        hhit.2 b
    rw [headOut, ite_eq_right (by simpa using hhit)] at hhead
    obtain ⟨st₂, b₂, hbr, h₀, hph₂, hst₂, hln₂, hocc, hsg₂, hB₂⟩ := branches_arc
      (st := { st with t₁ := X, t₂ := Y }) hOc hsgn (by st_bounded) hlen
      (by dsimp only; omega) hw harc false
    obtain ⟨l, st', b', hbr', h0, h1⟩ := ih st₂ (h₀ ▸ hO₀) hocc.2 (hsg₂ ▸ Bool.toNat_le _)
      (hph₂ ▸ hph) hB₂ (hln₂ ▸ hlen) (by simp only [hst₂, hln₂]; omega)
      (by rwa [hsg₂, decide_toNat_eq_one, hph₂]) b₂
    refine ⟨l, st', b', (branches_of_reaches' hhead (by omega) b false).trans (hbr.trans hbr'),
      fun hp => ?_, fun hp => h1 (hph₂ ▸ hp)⟩
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h0 (hph₂ ▸ hp)
    exact ⟨h₁, h₂, h₃, h₄.trans h₀, h₅.trans hln₂, h₆, h₇, h₈⟩

/-- A formula has at most as many occurrences of literals as its encoding has bits. -/
theorem length_flatten_le_length_encCNF (φ : CNF ℕ) : φ.flatten.length ≤ (encCNF φ).length := by
  rw [encCNF_eq_flatMap]
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc : c.length ≤ (c.flatMap fun l => literalBits l.1 l.2).length := by
      induction c with
      | nil => simp
      | cons l c ihc => simp [length_literalBits]; omega
    simp only [List.flatten_cons, List.flatMap_cons, List.length_append, length_clauseBits]; omega

/-- A path of the implication graph has a version with at most as many arcs as the encoding of
the formula has bits. -/
private theorem exists_relatesInSteps {ℓ ℓ' : Literal ℕ}
    (h : Relation.ReflTransGen φ.Implies ℓ ℓ') :
    ∃ m ≤ (encCNF φ).length, Relation.RelatesInSteps φ.Implies ℓ ℓ' m := by
  have hsub : {y | Relation.ReflTransGen φ.Implies ℓ y} ⊆
      insert ℓ (↑φ.flatten.toFinset : Set (Literal ℕ)) := fun y hy =>
    match Relation.ReflTransGen.cases_tail hy with
    | .inl rfl => Set.mem_insert _ _
    | .inr ⟨_, _, c, hc, _, hy, _⟩ => Set.mem_insert_of_mem _ (by simpa using ⟨c, hc, hy⟩)
  have hcard : {y | Relation.ReflTransGen φ.Implies ℓ y}.encard ≤
      ((φ.flatten.length : ℕ) : ℕ∞) + 1 :=
    calc _ ≤ (insert ℓ (↑φ.flatten.toFinset : Set (Literal ℕ))).encard :=
          Set.encard_le_encard hsub
      _ ≤ (↑φ.flatten.toFinset : Set (Literal ℕ)).encard + 1 := Set.encard_insert_le _ _
      _ ≤ _ := by
        rw [Set.encard_coe_eq_coe_finsetCard]
        gcongr
        exact_mod_cast List.toFinset_card_le _
  obtain ⟨m, hm, hsteps⟩ := h.relatesWithinSteps_of_encard_le hcard
  exact ⟨m, hm.trans (length_flatten_le_length_encCNF φ), hsteps⟩

/-- Guessing the initial literal occurrence `(x, false)` in mode B and reaching the walk head at
label `35`. -/
private theorem branches_modeB_init {x m₁ : ℕ}
    (hpath₁ : Relation.RelatesInSteps φ.Implies (x, true) (x, false) (m₁ + 1)) :
    ∃ o ≤ bnd φ, InfixAt (encCNF φ) o (literalBits x false) ∧
      Branches (P := decider) (w := encCNF φ) decider.init
        (35, ({ len := (encCNF φ).length, p := o, o₀ := o, cur := o, sgn := 1 } : St).regs
          (false : Bool).toNat) := by
  obtain ⟨ℓ₁, ⟨c, hcφ, hneg, -, -⟩, -⟩ := hpath₁.succ'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcφ
  obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hneg
  have hB : ({ len := (encCNF φ).length } : St).Bounded (bnd φ) := by st_bounded
  obtain ⟨q, hq, hqB, hscan⟩ := branches_scan (φ := φ) (l₀ := 20) (skip := 22) (inspect := 27)
    rfl rfl codeAt_skipClause₂₂ (by omega) (by omega) φ (clausesAt_encCNF φ) rfl hB i hi false
    false
  obtain ⟨o, ho, hlit⟩ := branches_lit (φ[i]) hq
    (st := { ({ len := (encCNF φ).length } : St) with p := q }) rfl (by st_bounded) j hj false
    false
  rw [hjx] at ho
  have hoB := le_bnd_of_infixAt ho (literalBits_ne_nil _ _)
  exact ⟨o, le_trans (Nat.le_add_right _ _) hoB, ho, (branches_to_scan (b := true)).trans
    (hscan.trans (hlit.trans (branches_of_reaches' (reaches_pick (st :=
      { ({ len := (encCNF φ).length } : St) with p := o }) rfl (by st_bounded)) (by omega)
      false false)))⟩

/-- **An accepting branch for a variable `x` with a path from `x` to `¬x` and one back**, for a
formula whose clauses have one or two literals. -/
theorem branches_modeB (hw : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 2) {x : ℕ}
    (h₁ : Relation.ReflTransGen φ.Implies (x, true) (x, false))
    (h₂ : Relation.ReflTransGen φ.Implies (x, false) (x, true)) :
    ∃ s, Branches (P := decider) (w := encCNF φ) decider.init s ∧
      decider.instr s.1 = .accept := by
  obtain ⟨m₁, hm₁, hpath₁⟩ := exists_relatesInSteps h₁
  obtain ⟨m₂, hm₂, hpath₂⟩ := exists_relatesInSteps h₂
  rcases m₁ with _ | m₁
  · simp at hpath₁
  rcases m₂ with _ | m₂
  · simp at hpath₂
  obtain ⟨o, hoB, ho, hto35⟩ := branches_modeB_init hpath₁
  obtain ⟨_, st₁, b₁, hbr₁, h0, -⟩ := branches_walk hw (m₁ + 1)
    { len := (encCNF φ).length, p := o, o₀ := o, cur := o, sgn := 1 } ho ho le_rfl (Nat.zero_le _)
    (by st_bounded) rfl
    (Nat.zero_add _ ▸ hm₁) hpath₁ false
  obtain ⟨rfl, hph₁, hst₁, ho₁, hln₁, hB₁, hsg₁, _, hcur₁⟩ := h0 rfl
  obtain ⟨ℓ₂, harc, hrest⟩ := hpath₂.succ'
  obtain ⟨st₂, b₃, hbr₂, h₂₀, h₂₁, h₂₂, h₂₃, hocc, hsg₂, hB₂⟩ := branches_arc hcur₁
    (by omega) hB₁ hln₁
    (by simp only [hst₁, hln₁]; omega) hw
    (by simpa [hsg₁] using harc) b₁
  obtain ⟨_, _, _, hbr₃, -, h1⟩ := branches_walk hw m₂ st₂
    (by rwa [h₂₀, ho₁]) hocc.2
    (hsg₂ ▸ Bool.toNat_le _) (h₂₁.trans hph₁ ▸ le_rfl) hB₂ (h₂₃.trans hln₁)
    (by simp only [h₂₂, hst₁, h₂₃, hln₁]; omega)
    (by rwa [hsg₂, decide_toNat_eq_one, h₂₁, hph₁]) b₃
  obtain rfl := h1 (h₂₁.trans hph₁)
  exact ⟨_, hto35.trans (hbr₁.trans (hbr₂.trans hbr₃)), rfl⟩

/-- **The decider accepts exactly the formulas outside `TwoSAT`**: some branch accepts exactly
then. -/
theorem accepts_decider_iff :
    (∃ s, Branches (P := decider) (w := encCNF φ) decider.init s ∧
      decider.instr s.1 = .accept) ↔ φ ∉ TwoSAT := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨s, ⟨choices, rfl⟩, hacc⟩
    exact ((allBranches_decider (φ := φ)).replay choices).2 (by simp [halted, hacc, Instr.halts])
      hacc
  · rcases notMem_TwoSAT_iff.mp h with ⟨c, hc, hlen⟩ | hnil | ⟨x, h₁, h₂⟩
    · exact branches_modeA hc (.inr hlen)
    · exact branches_modeA hnil (.inl rfl)
    · by_cases hbad : ∃ c ∈ φ, c.length = 0 ∨ 3 ≤ c.length
      · obtain ⟨c, hc, hw⟩ := hbad; exact branches_modeA hc hw
      · push Not at hbad
        exact branches_modeB (fun c hc => by have := hbad c hc; omega) h₁ h₂

end TwoSAT

/-- **The complement of `TwoSAT` is decided in nondeterministic logarithmic space**: one
nondeterministic machine decides it within space logarithmic in the length of the encoding,
every branch halting. -/
theorem TwoSAT.exists_decidesInLogSpace_compl :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : _root_.Turing.MultiTapeNTM k Bool State)
      (c : ℕ), ntm.DecidesInSpace encCNF TwoSATᶜ fun φ =>
        c * (Nat.log2 (encCNF φ).length + 1) :=
  _root_.Turing.CounterProgram.exists_decidesInLogSpace_of_allBranches TwoSAT.decider 1
    (fun φ => by rw [pow_one]; exact TwoSAT.allBranches_decider (φ := φ))
    fun φ hφ => (TwoSAT.accepts_decider_iff (φ := φ)).2 hφ

end Cslib.Complexity
