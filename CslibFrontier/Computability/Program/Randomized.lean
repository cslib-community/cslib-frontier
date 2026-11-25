/-
Copyright (c) 2026 Renfei Zhou, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Program.Assemble
public import CslibFrontier.Languages.Probabilistic.QueryCount.Support

/-!
# Randomized structured programs

The structured control flow of `Code` can interpret machine operations as probabilistic
computations. `ExecRand` describes successful executions on every path and pairs each resulting
data state with its exact instruction count. The operation interpretation returns `none` when
an operation faults and `some` computation for an operation that always returns a data state.
Deterministic successful operations can return pure computations. Sampling costs one instruction
when the flat machine implements the sampling operation as a primitive instruction.

## Main definitions

* `ExecRand`: randomized execution with exact per-path instruction counts.
* `RandomizedFlatMachine`: a flat machine's probabilistic step laws.

## Main results

* `ExecRand.runRand_assemble`: equality of the clocked flat and structured computations.

The structured semantics and assembly proof generalize those in
`CslibFrontier.Computability.WordRAM.Randomized.Structured`.
-/

public section

namespace Cslib.Program

universe u v w i

variable {I : InstructionSet.{u, v, w}}

-- The probabilistic evaluation returns none for a fault.
variable (evalRand : I.Op → I.Data → Option (ProbComp I.Data))

/-- Exact randomized execution of structured code, with every branch of the computation
terminating successfully. Each primitive operation costs one flat instruction. -/
inductive ExecRand : Code I.Op I.Test → I.Data → ProbComp (I.Data × ℕ) → Prop where
  /-- Empty code costs zero instructions. -/
  | skip {x : I.Data} : ExecRand .skip x (pure (x, 0))
  /-- An operation returns a probabilistic data state and uses one instruction. -/
  | op {o : I.Op} {x : I.Data} {m : ProbComp I.Data} (h : evalRand o x = some m) :
      ExecRand (.op o) x ((fun y => (y, 1)) <$> m)
  /-- Sequencing composes the two computations and adds their instruction counts. -/
  | seq {c₁ c₂ : Code I.Op I.Test} {x : I.Data} {m₁ : ProbComp (I.Data × ℕ)}
      {m₂ : I.Data → ProbComp (I.Data × ℕ)}
      (h₁ : ExecRand c₁ x m₁)
      (h₂ : ∀ z ∈ m₁.support, ExecRand c₂ z.1 (m₂ z.1)) :
      ExecRand (.seq c₁ c₂) x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2))
  /-- Taking the positive branch adds `1` instruction for the branch test. -/
  | branch_pos {c : I.Test} {pos neg : Code I.Op I.Test} {x : I.Data} {m : ProbComp (I.Data × ℕ)}
      (hc : I.Holds c x) (h : ExecRand pos x m) :
      ExecRand (.branch c pos neg) x ((fun z => (z.1, z.2 + 1)) <$> m)
  /-- Taking the negative branch adds `2` instructions (branch test and jump past `pos`). -/
  | branch_neg {c : I.Test} {pos neg : Code I.Op I.Test} {x : I.Data} {m : ProbComp (I.Data × ℕ)}
      (hc : ¬I.Holds c x) (h : ExecRand neg x m) :
      ExecRand (.branch c pos neg) x ((fun z => (z.1, z.2 + 2)) <$> m)
  /-- Exiting a loop when the condition fails takes `2` instructions (branch test and exit jump). -/
  | loop_exit {c : I.Test} {body : Code I.Op I.Test} {x : I.Data} (hc : ¬I.Holds c x) :
      ExecRand (.loop c body) x (pure (x, 2))
  /-- Entering a loop executes `body`, jumps back to the header, and continues the loop, adding `2`
  instructions for the branch test and back-jump. -/
  | loop_iter {c : I.Test} {body : Code I.Op I.Test} {x : I.Data} {mb : ProbComp (I.Data × ℕ)}
      {ml : I.Data → ProbComp (I.Data × ℕ)}
      (hc : I.Holds c x)
      (hb : ExecRand body x mb)
      (hl : ∀ z ∈ mb.support, ExecRand (.loop c body) z.1 (ml z.1)) :
      ExecRand (.loop c body) x (do
        let z₁ ← mb
        let z₂ ← ml z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))
  /-- Exiting a repeat-until loop takes its successful test. -/
  | loopUntil_exit {c : I.Test} {body : Code I.Op I.Test} {x : I.Data} (hc : I.Holds c x) :
      ExecRand (.loopUntil c body) x (pure (x, 1))
  /-- A failed test, body execution and back-jump continue the repeat-until loop. -/
  | loopUntil_iter {c : I.Test} {body : Code I.Op I.Test} {x : I.Data}
      {mb : ProbComp (I.Data × ℕ)} {ml : I.Data → ProbComp (I.Data × ℕ)}
      (hc : ¬I.Holds c x) (hb : ExecRand body x mb)
      (hl : ∀ z ∈ mb.support, ExecRand (.loopUntil c body) z.1 (ml z.1)) :
      ExecRand (.loopUntil c body) x (do
        let z₁ ← mb
        let z₂ ← ml z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))

/-- A randomized interpretation of a flat machine. The running configurations use the
flat program counter and data. A machine may also have halted or faulted configurations. -/
structure RandomizedFlatMachine (F : FlatMachine.{u, v, w, i} I) where
  /-- Full configuration type, including any terminal configurations. -/
  Config : Type u
  /-- Configuration at the given instruction label and data state. -/
  running : ℕ → I.Data → Config
  /-- One probabilistic step. -/
  step : List F.Instr → Config → ProbComp Config
  /-- A successful data operation falls through with its sampled result. -/
  step_op {p : List F.Instr} {pc : ℕ} {o : I.Op} {x : I.Data} {m : ProbComp I.Data} :
    p[pc]? = some (F.op o) → evalRand o x = some m →
      step p (running pc x) = running (pc + 1) <$> m
  /-- An unconditional jump changes only the program counter. -/
  step_goto {p : List F.Instr} {pc label : ℕ} {x : I.Data} :
    p[pc]? = some (F.goto label) → step p (running pc x) = pure (running label x)
  /-- A satisfied test jumps to its target. -/
  step_jumpIf_pos {p : List F.Instr} {pc label : ℕ} {t : I.Test} {x : I.Data} :
    p[pc]? = some (F.jumpIf t label) → I.Holds t x →
      step p (running pc x) = pure (running label x)
  /-- A failed test falls through. -/
  step_jumpIf_neg {p : List F.Instr} {pc label : ℕ} {t : I.Test} {x : I.Data} :
    p[pc]? = some (F.jumpIf t label) → ¬I.Holds t x →
      step p (running pc x) = pure (running (pc + 1) x)

namespace RandomizedFlatMachine

variable {evalRand} {F : FlatMachine.{u, v, w, i} I}
  (R : RandomizedFlatMachine.{u, v, w, i} evalRand F)

/-- Run the flat program for the given instruction budget. -/
def run (p : List F.Instr) : ℕ → R.Config → ProbComp R.Config
  | 0, cfg => pure cfg
  | n + 1, cfg => R.step p cfg >>= run p n

/-- A zero budget returns the initial configuration. -/
theorem run_zero (p : List F.Instr) (cfg : R.Config) : R.run p 0 cfg = pure cfg := by
  rw [run]

/-- A positive budget takes one step and runs the remaining budget. -/
theorem run_succ (p : List F.Instr) (n : ℕ) (cfg : R.Config) :
    R.run p (n + 1) cfg = (R.step p cfg >>= R.run p n) := by
  rw [run]

variable {p : List F.Instr} {pc label k : ℕ} {x : I.Data} {t : I.Test}

private theorem runRand_step_jump (hp : p[pc]? = some (F.goto label)) :
    R.run p (k + 1) (R.running pc x) = R.run p k (R.running label x) := by
  rw [run, R.step_goto hp, pure_bind]

private theorem runRand_step_jumpIf_pos (hp : p[pc]? = some (F.jumpIf t label))
    (ht : I.Holds t x) :
    R.run p (k + 1) (R.running pc x) = R.run p k (R.running label x) := by
  rw [run, R.step_jumpIf_pos hp ht, pure_bind]

private theorem runRand_step_jumpIf_neg (hp : p[pc]? = some (F.jumpIf t label))
    (ht : ¬I.Holds t x) :
    R.run p (k + 1) (R.running pc x) = R.run p k (R.running (pc + 1) x) := by
  rw [run, R.step_jumpIf_neg hp ht, pure_bind]

private theorem bound_map {m : ProbComp (I.Data × ℕ)} {extra T : ℕ}
    (hT : ∀ z ∈ ((fun z => (z.1, z.2 + extra)) <$> m).support, z.2 ≤ T) :
    extra ≤ T ∧ ∀ z ∈ m.support, z.2 + extra ≤ T := by
  have hm : ∀ z ∈ m.support, z.2 + extra ≤ T := fun z hz =>
    hT (z.1, z.2 + extra) (OracleComp.mem_supportWith_map_iff.mpr ⟨z, hz, rfl⟩)
  obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty m
  exact ⟨(Nat.le_add_left _ _).trans (hm z₀ hz₀), hm⟩

private theorem bound_seq {m₁ : ProbComp (I.Data × ℕ)} {m₂ : I.Data → ProbComp (I.Data × ℕ)}
    {extra T : ℕ} (bound : ∀ z ∈ (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2 + extra) : ProbComp (I.Data × ℕ)).support, z.2 ≤ T)
    {z₁ z₂ : I.Data × ℕ} (h₁ : z₁ ∈ m₁.support) (h₂ : z₂ ∈ (m₂ z₁.1).support) :
    z₁.2 + z₂.2 + extra ≤ T :=
  bound _ (OracleComp.mem_supportWith_bind_iff.mpr
    ⟨z₁, h₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, h₂, rfl⟩⟩)

private theorem run_loop_iter {p : List F.Instr} {pc bodyPC exitPC T : ℕ} {x : I.Data}
    {body : Code I.Op I.Test} {mb : ProbComp (I.Data × ℕ)} {ml : I.Data → ProbComp (I.Data × ℕ)}
    (hstep : ∀ {k}, R.run p (k + 1) (R.running pc x) = R.run p k (R.running bodyPC x))
    (hbody : Contains p bodyPC (body.assemble F bodyPC))
    (back : p[bodyPC + body.size]? = some (F.goto pc))
    (runBody : ∀ {T}, Contains p bodyPC (body.assemble F bodyPC) →
      (∀ z ∈ mb.support, z.2 ≤ T) → R.run p T (R.running bodyPC x) = (do
        let z ← mb
        R.run p (T - z.2) (R.running (bodyPC + body.size) z.1)))
    (runRest : ∀ y ∈ mb.support, ∀ {T}, (∀ z ∈ (ml y.1).support, z.2 ≤ T) →
      R.run p T (R.running pc y.1) = (do
        let z ← ml y.1
        R.run p (T - z.2) (R.running exitPC z.1)))
    (hT : ∀ z ∈ (do
      let z₁ ← mb
      let z₂ ← ml z₁.1
      pure (z₂.1, z₁.2 + z₂.2 + 2) : ProbComp (I.Data × ℕ)).support, z.2 ≤ T) :
    R.run p T (R.running pc x) =
      ((do
        let z₁ ← mb
        let z₂ ← ml z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2)) >>= fun z =>
          R.run p (T - z.2) (R.running exitPC z.1)) := by
  have bound := @bound_seq I mb ml 2 T hT
  obtain ⟨y₀, hy₀⟩ := ProbComp.support_nonempty mb
  obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty (ml y₀.1)
  have := bound hy₀ hz₀
  obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
  rw [hstep]
  simp only [bind_assoc, pure_bind]
  have room : ∀ y ∈ mb.support, y.2 + 1 ≤ k := fun y hy => by
    obtain ⟨z, hz⟩ := ProbComp.support_nonempty (ml y.1)
    have := bound hy hz
    omega
  rw [runBody hbody (fun y hy => Nat.le_of_succ_le (room y hy))]
  refine OracleComp.bind_congr_on_support fun y hy => ?_
  have := room y hy
  rw [show k - y.2 = (k - y.2 - 1) + 1 by omega, runRand_step_jump R back]
  have hRest : ∀ z ∈ (ml y.1).support, z.2 ≤ k - y.2 - 1 := fun z hz => by
    have := bound hy hz; omega
  rw [runRest y hy hRest]
  refine OracleComp.bind_congr_on_support fun z hz => ?_
  have := bound hy hz
  congr 1
  omega

end RandomizedFlatMachine

open RandomizedFlatMachine in
/-- Running a contained compiled program agrees with performing the structured computation
and then continuing after its block for the remaining budget on each path. -/
theorem ExecRand.runRand_assemble {evalRand} {F : FlatMachine.{u, v, w, i} I}
    (R : RandomizedFlatMachine.{u, v, w, i} evalRand F) {p : List F.Instr}
    {c : Code I.Op I.Test} {x : I.Data} {m : ProbComp (I.Data × ℕ)} {pc T : ℕ}
    (h : ExecRand evalRand c x m) (hp : Contains p pc (c.assemble F pc))
    (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    R.run p T (R.running pc x) = (do
      let z ← m
      R.run p (T - z.2) (R.running (pc + c.size) z.1)) := by
  induction h generalizing pc T with
  | skip => simp [Code.size]
  | @op o x m ho =>
    obtain ⟨y, hy⟩ := ProbComp.support_nonempty m
    have h1 := hT (y, 1) (OracleComp.mem_supportWith_map_iff.mpr ⟨y, hy, rfl⟩)
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [run, R.step_op hp.head ho, ← bind_pure_comp, bind_assoc, ← bind_pure_comp, bind_assoc]
    simp only [pure_bind, Code.size, Nat.add_sub_cancel]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have bound := @bound_seq I m₁ m₂ 0 T hT
    have hT₁ : ∀ z₁ ∈ m₁.support, z₁.2 ≤ T := fun z₁ hz₁ => by
      obtain ⟨z₂, hz₂⟩ := ProbComp.support_nonempty (m₂ z₁.1)
      have := bound hz₁ hz₂
      omega
    rw [ih₁ hp.append_left hT₁, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
    have hT₂ : ∀ z₂ ∈ (m₂ z₁.1).support, z₂.2 ≤ T - z₁.2 := fun z₂ hz₂ => by
      have := bound hz₁ hz₂; omega
    rw [ih₂ z₁ hz₁ (by simpa using hp.append_right) hT₂, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z₂ _ => ?_
    simp only [pure_bind, Code.size, Nat.sub_sub, Nat.add_assoc]
  | @branch_pos cond pos neg x m hc _ ih =>
    obtain ⟨h1, hm⟩ := bound_map hT
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_step_jumpIf_pos R hp.head hc]
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble F (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    rw [ih hc' (fun z hz => Nat.le_of_add_le_add_right (hm z hz)), ← bind_pure_comp, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z _ => ?_
    simp only [pure_bind, Code.size, Nat.add_sub_add_right]
    rw [show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
  | @branch_neg cond pos neg x m hc _ ih =>
    obtain ⟨h2, hm⟩ := bound_map hT
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_step_jumpIf_neg R hp.head hc]
    have hTm : ∀ z ∈ m.support, z.2 ≤ k := fun z hz => by have := hm z hz; omega
    rw [ih hp.cons_tail.append_left hTm, ← bind_pure_comp, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z hz => ?_
    have := hm z hz
    have hj : p[pc + 1 + neg.size]? = some (F.goto (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble F (pc + 1))).head
    simp only [pure_bind, Code.size]
    rw [show k - z.2 = (k + 1 - (z.2 + 2)) + 1 by omega, runRand_step_jump R hj,
      show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
  | @loop_exit cond body x hc =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by have := hT (x, 2) rfl; omega⟩
    rw [show k + 2 = (k + 1) + 1 by omega, runRand_step_jumpIf_neg R hp.head hc,
      runRand_step_jump R hp.cons_tail.head]
    simp only [pure_bind, Code.size, show k + 1 + 1 - 2 = k by omega, Nat.add_assoc]
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    exact run_loop_iter R (runRand_step_jumpIf_pos R hp.head hc)
      (by simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left)
      (by simpa using hp.cons_tail.cons_tail.append_right.head)
      (fun h hT => ihb h hT) (fun y hy {_} hT => ihl y hy hp hT) hT
  | @loopUntil_exit cond body x hc =>
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by have := hT (x, 1) rfl; omega⟩
    rw [runRand_step_jumpIf_pos R hp.head hc]
    simp only [pure_bind, Code.size, Nat.add_sub_cancel, Nat.add_assoc]
  | @loopUntil_iter cond body x mb ml hc _ _ ihb ihl =>
    exact run_loop_iter R (runRand_step_jumpIf_neg R hp.head hc)
      (by simpa using hp.cons_tail.append_left)
      (by simpa using hp.cons_tail.append_right.head)
      (fun h hT => ihb h hT) (fun y hy {_} hT => ihl y hy hp hT) hT

end Cslib.Program
