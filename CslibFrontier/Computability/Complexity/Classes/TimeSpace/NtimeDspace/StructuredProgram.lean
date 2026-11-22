/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.BigCounterProgram

/-!
# Structured counter programs

A small structured language over Complexitylib counter programs: assignment,
sequencing, conditionals and loops on a comparison, and branching on an input
bit. A statement compiles to a block of instructions placed at any label; the
block exits by falling through to the label after it.

The big-step relation `Exec` carries a register invariant `Inv`, required at
every executed instruction. `Exec.reaches` turns a derivation into a run of the
compiled code through configurations satisfying `Inv`, which is the form used
by the large-register compiler theorem.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Structured

open _root_.Turing _root_.Turing.CounterProgram

/-- Structured statements. Comparisons test `x < y`. -/
inductive Stmt : Type where
  | skip
  | assign (i : ℕ) (e : Expr)
  | seq (a b : Stmt)
  | ite (x y : Expr) (yes no : Stmt)
  | loop (x y : Expr) (body : Stmt)
  | read (e : Expr) (onTrue onFalse onEnd : Stmt)

/-- An unconditional jump, as a comparison whose branches agree. -/
def jump (target : ℕ) : Instr := .lt (.const 0) (.const 0) target target

namespace Stmt

/-- The number of instructions of a compiled statement. -/
def length : Stmt → ℕ
  | skip => 0
  | assign .. => 1
  | seq a b => a.length + b.length
  | ite _ _ yes no => yes.length + no.length + 2
  | loop _ _ body => body.length + 2
  | read _ t f n => t.length + f.length + n.length + 3

/-- The instructions of a statement placed at label `b`. -/
def compile : Stmt → ℕ → List Instr
  | skip, _ => []
  | assign i e, b => [.assign i e (b + 1)]
  | seq a c, b => a.compile b ++ c.compile (b + a.length)
  | ite x y yes no, b =>
      [.lt x y (b + 1) (b + yes.length + 2)] ++ yes.compile (b + 1) ++
        [jump (b + yes.length + no.length + 2)] ++ no.compile (b + yes.length + 2)
  | loop x y body, b =>
      [.lt x y (b + 1) (b + body.length + 2)] ++ body.compile (b + 1) ++ [jump b]
  | read e t f n, b =>
      [.read e (b + 1) (b + t.length + 2) (b + t.length + f.length + 3)] ++
        t.compile (b + 1) ++ [jump (b + t.length + f.length + n.length + 3)] ++
        f.compile (b + t.length + 2) ++ [jump (b + t.length + f.length + n.length + 3)] ++
        n.compile (b + t.length + f.length + 3)

@[simp] theorem length_compile (s : Stmt) (b : ℕ) : (s.compile b).length = s.length := by
  induction s generalizing b <;> simp [compile, length, *] <;> omega

end Stmt

open Stmt

variable (w : List Bool) (Inv : List ℕ → Prop)

/-- Big-step execution on input `w`. Every executed instruction, including the
jumps that close branches and loop bodies, requires `Inv` of the registers it
sees. -/
inductive Exec : Stmt → List ℕ → List ℕ → Prop where
  | skip (r : List ℕ) : Exec .skip r r
  | assign {i : ℕ} {e : Expr} {r : List ℕ} : Inv r → Exec (.assign i e) r (r.set i (e.eval r))
  | seq {a c : Stmt} {r r' r'' : List ℕ} : Exec a r r' → Exec c r' r'' → Exec (.seq a c) r r''
  | ite_yes {x y : Expr} {yes no : Stmt} {r r' : List ℕ} : Inv r → x.eval r < y.eval r →
      Exec yes r r' → Inv r' → Exec (.ite x y yes no) r r'
  | ite_no {x y : Expr} {yes no : Stmt} {r r' : List ℕ} : Inv r → ¬ x.eval r < y.eval r →
      Exec no r r' → Exec (.ite x y yes no) r r'
  | loop_step {x y : Expr} {body : Stmt} {r r' r'' : List ℕ} : Inv r → x.eval r < y.eval r →
      Exec body r r' → Inv r' → Exec (.loop x y body) r' r'' → Exec (.loop x y body) r r''
  | loop_done {x y : Expr} {body : Stmt} {r : List ℕ} : Inv r → ¬ x.eval r < y.eval r →
      Exec (.loop x y body) r r
  | read_true {e : Expr} {t f n : Stmt} {r r' : List ℕ} : Inv r → w[e.eval r]? = some true →
      Exec t r r' → Inv r' → Exec (.read e t f n) r r'
  | read_false {e : Expr} {t f n : Stmt} {r r' : List ℕ} : Inv r → w[e.eval r]? = some false →
      Exec f r r' → Inv r' → Exec (.read e t f n) r r'
  | read_end {e : Expr} {t f n : Stmt} {r r' : List ℕ} : Inv r → w[e.eval r]? = none →
      Exec n r r' → Exec (.read e t f n) r r'

/-- The configurations passed through: a running instruction with registers
satisfying the invariant. -/
def Good (P : CounterProgram) (Inv : List ℕ → Prop) (c : Config) : Prop :=
  (P.instr c.1).IsStep ∧ Inv c.2

variable {w Inv} {P : CounterProgram}

theorem reaches_assign {c i next : ℕ} {e : Expr} {r : List ℕ} {s' : Config}
    (hc : P.instr c = .assign i e next) (hI : Inv r)
    (h : P.Reaches w (Good P Inv) (next, r.set i (e.eval r)) s') :
    P.Reaches w (Good P Inv) (c, r) s' :=
  Reaches.head ⟨by rw [hc]; trivial, hI⟩ (by rwa [P.step_assign w hc])

theorem reaches_lt {c yes no : ℕ} {x y : Expr} {r : List ℕ} {s' : Config}
    (hc : P.instr c = .lt x y yes no) (hI : Inv r)
    (h : P.Reaches w (Good P Inv) (if x.eval r < y.eval r then yes else no, r) s') :
    P.Reaches w (Good P Inv) (c, r) s' :=
  Reaches.head ⟨by rw [hc]; trivial, hI⟩ (by rwa [P.step_lt w hc])

theorem reaches_jump {c target : ℕ} {r : List ℕ} {s' : Config}
    (hc : P.instr c = jump target) (hI : Inv r)
    (h : P.Reaches w (Good P Inv) (target, r) s') :
    P.Reaches w (Good P Inv) (c, r) s' :=
  reaches_lt hc hI (by simpa using h)

theorem reaches_read {c onTrue onFalse onEnd : ℕ} {e : Expr} {r : List ℕ} {s' : Config}
    (hc : P.instr c = .read e onTrue onFalse onEnd) (hI : Inv r)
    (h : P.Reaches w (Good P Inv) (readLabel onTrue onFalse onEnd w[e.eval r]?, r) s') :
    P.Reaches w (Good P Inv) (c, r) s' :=
  Reaches.head ⟨by rw [hc]; trivial, hI⟩ (by rwa [P.step_read w hc])

theorem codeAt_singleton {b : ℕ} {ins : Instr} : P.CodeAt b [ins] ↔ P.instr b = ins := by
  simp [codeAt_cons, codeAt_nil]

theorem codeAt_of_eq {b b' : ℕ} {l : List Instr} (h : P.CodeAt b l) (e : b = b') :
    P.CodeAt b' l := e ▸ h

theorem instr_of_eq {b b' : ℕ} {ins : Instr} (h : P.CodeAt b [ins]) (e : b = b') :
    P.instr b' = ins := codeAt_singleton.mp (codeAt_of_eq h e)

theorem reaches_refl_of_eq {c c' : ℕ} {r : List ℕ} (e : c = c') :
    P.Reaches w (Good P Inv) (c, r) (c', r) := e ▸ Reaches.refl _

/-- **Structured execution is a run of the compiled code.** -/
theorem Exec.reaches {s : Stmt} {r r' : List ℕ} (h : Exec w Inv s r r') :
    ∀ {b : ℕ}, P.CodeAt b (s.compile b) →
      P.Reaches w (Good P Inv) (b, r) (b + s.length, r') := by
  induction h with
  | skip r => intro b _; exact reaches_refl_of_eq (by simp [Stmt.length])
  | assign hI =>
    intro b code
    exact reaches_assign (codeAt_singleton.mp code) hI (reaches_refl_of_eq (by simp [Stmt.length]))
  | seq _ _ iha ihc =>
    intro b code
    rw [compile, codeAt_append, length_compile] at code
    exact ((iha code.1).trans (ihc code.2)).trans
      (reaches_refl_of_eq (by simp [Stmt.length]; omega))
  | @ite_yes x y yes no r r' hI hlt _ hI' ih =>
    intro b code
    rw [compile, codeAt_append, codeAt_append, codeAt_append] at code
    obtain ⟨⟨⟨h0, hy⟩, hj⟩, -⟩ := code
    refine reaches_lt (codeAt_singleton.mp h0) hI ?_
    simp only [hlt, ↓reduceIte]
    refine (ih (codeAt_of_eq hy (by simp))).trans ?_
    exact reaches_jump (instr_of_eq hj (by simp; omega)) hI'
      (reaches_refl_of_eq (by simp [Stmt.length]; omega))
  | @ite_no x y yes no r r' hI hlt _ ih =>
    intro b code
    rw [compile, codeAt_append, codeAt_append, codeAt_append] at code
    obtain ⟨⟨⟨h0, -⟩, -⟩, hn⟩ := code
    refine reaches_lt (codeAt_singleton.mp h0) hI ?_
    simp only [hlt, ↓reduceIte]
    exact (ih (codeAt_of_eq hn (by simp; omega))).trans
      (reaches_refl_of_eq (by simp [Stmt.length]; omega))
  | @loop_step x y body r r' r'' hI hlt _ hI' _ ihb ihl =>
    intro b code
    have code' := code
    rw [compile, codeAt_append, codeAt_append] at code'
    obtain ⟨⟨h0, hbody⟩, hj⟩ := code'
    refine reaches_lt (codeAt_singleton.mp h0) hI ?_
    simp only [hlt, ↓reduceIte]
    refine (ihb (codeAt_of_eq hbody (by simp))).trans ?_
    exact reaches_jump (instr_of_eq hj (by simp; omega)) hI' (ihl code)
  | @loop_done x y body r hI hlt =>
    intro b code
    rw [compile, codeAt_append, codeAt_append] at code
    refine reaches_lt (codeAt_singleton.mp code.1.1) hI ?_
    simp only [hlt, ↓reduceIte]
    exact reaches_refl_of_eq (by simp [Stmt.length]; omega)
  | @read_true e t f n r r' hI hb _ hI' ih =>
    intro b code
    rw [compile, codeAt_append, codeAt_append, codeAt_append, codeAt_append,
      codeAt_append] at code
    obtain ⟨⟨⟨⟨⟨h0, ht⟩, hj⟩, -⟩, -⟩, -⟩ := code
    refine reaches_read (codeAt_singleton.mp h0) hI ?_
    simp only [hb, readLabel]
    refine (ih (codeAt_of_eq ht (by simp))).trans ?_
    exact reaches_jump (instr_of_eq hj (by simp; omega)) hI'
      (reaches_refl_of_eq (by simp [Stmt.length]; omega))
  | @read_false e t f n r r' hI hb _ hI' ih =>
    intro b code
    rw [compile, codeAt_append, codeAt_append, codeAt_append, codeAt_append,
      codeAt_append] at code
    obtain ⟨⟨⟨⟨⟨h0, -⟩, -⟩, hf⟩, hj⟩, -⟩ := code
    refine reaches_read (codeAt_singleton.mp h0) hI ?_
    simp only [hb, readLabel]
    refine (ih (codeAt_of_eq hf (by simp; omega))).trans ?_
    exact reaches_jump (instr_of_eq hj (by simp; omega)) hI'
      (reaches_refl_of_eq (by simp [Stmt.length]; omega))
  | @read_end e t f n r r' hI hb _ ih =>
    intro b code
    rw [compile, codeAt_append, codeAt_append, codeAt_append, codeAt_append,
      codeAt_append] at code
    obtain ⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, -⟩, hn⟩ := code
    refine reaches_read (codeAt_singleton.mp h0) hI ?_
    simp only [hb, readLabel]
    exact (ih (codeAt_of_eq hn (by simp; omega))).trans
      (reaches_refl_of_eq (by simp [Stmt.length]; omega))

end Cslib.Complexity.NtimeDspace.Structured

namespace Cslib.Complexity.NtimeDspace.Structured

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.CounterProgram Stmt

/-- A decider: run the statement, then accept iff register `result` is positive. -/
def decider (s : Stmt) (result registers : ℕ) : CounterProgram where
  code := s.compile 0 ++
    [.lt (.reg result) (.const 1) (s.length + 1) (s.length + 2), .halt [false], .halt [true]]
  registers := registers

/-- **Structured deciders run in the space of their registers.** If, on every
encoded input, the statement executes from zero registers to final registers
whose `result` register is positive exactly on members of `L`, with encoded
registers below `c * S a` at every executed instruction, then `L` is decidable
in simultaneous time `2^(C * S a)` and space `C * S a`. -/
theorem decidable_of_exec {α : Type} {enc : α ↪ List Bool} (L : Set α) (s : Stmt)
    (result registers : ℕ) (budget : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (final : α → List ℕ)
    (exec : ∀ a, Exec (enc a) (fun r => (encList encNat r).length ≤ c * budget a) s
      (List.replicate registers 0) (final a))
    (finalBound : ∀ a, (encList encNat (final a)).length ≤ c * budget a)
    (decides : ∀ a, (1 ≤ (final a).getD result 0 ↔ a ∈ L)) :
    ∃ C, DecidableInTimeAndSpace L enc (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  set P := decider s result registers
  refine BigCounterProgram.simultaneous_bounds_of_reaches P budget c logarithmic fun a => ?_
  have body : P.CodeAt 0 (s.compile 0) :=
    codeAt_of_eq (codeAt_of_code_eq (pre := [])
      (post := [.lt (.reg result) (.const 1) (s.length + 1) (s.length + 2), .halt [false],
        .halt [true]]) (by simp [P, decider])) rfl
  have tail : P.CodeAt s.length
      [.lt (.reg result) (.const 1) (s.length + 1) (s.length + 2), .halt [false], .halt [true]] :=
    codeAt_of_eq (codeAt_of_code_eq (pre := s.compile 0) (post := []) (by simp [P, decider]))
      (by simp)
  have run := (exec a).reaches (P := P) body
  simp only [Nat.zero_add] at run
  rw [codeAt_cons, codeAt_cons, codeAt_cons] at tail
  obtain ⟨hlt, hno, hyes, -⟩ := tail
  by_cases mem : a ∈ L
  · refine ⟨(s.length + 2, final a), run.trans (reaches_lt hlt (finalBound a) ?_), ?_,
      finalBound a⟩
    · have pos := (decides a).mpr mem
      rw [ite_eq_right (by simp only [Expr.eval_reg, Expr.eval_const]; omega)]
      exact Reaches.refl _
    · simp only [show s.length + 2 = s.length + 1 + 1 by omega, hyes, indicator, mem,
        ite_true]
      rfl
  · refine ⟨(s.length + 1, final a), run.trans (reaches_lt hlt (finalBound a) ?_), ?_,
      finalBound a⟩
    · have npos := (decides a).not.mpr mem
      rw [ite_eq_left (by simp only [Expr.eval_reg, Expr.eval_const]; omega)]
      exact Reaches.refl _
    · simp only [hno, indicator, mem, ite_false]
      rfl

end Cslib.Complexity.NtimeDspace.Structured
