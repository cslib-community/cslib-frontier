/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.PointerMachine.Local

/-! # Public interface tests for the local-address RAM compiler -/

set_option linter.privateModule false

open Cslib Cslib.WordRAM.Local

private abbrev model : PointerMachine.Model where
  Value := ℕ
  undefined := 0
  Op := Unit
  Test := Unit
  evalOp _ a _ := a
  evalTest _ a _ := a == 0

private abbrev TestCode := Program.Code (Op model 1 1) (Test model 1 1)

private def initial {n : ℕ} (a : Option (Fin n)) : Data model n 1 1 :=
  ⟨fun _ => a, fun _ => 7, fun _ => 0, fun _ => none⟩

private abbrev emptyState := initial (n := 0) none

example : Direction.next.move (1 : Fin 2) = none := by decide
example : Direction.prev.move (0 : Fin 2) = none := by decide

private def nullLoad : TestCode := .branch (.addrEq 0 0) (.op (.loadData 0 0)) .skip

example :
    PointerMachine.Executes (compile nullLoad).program
      (encode (emptyState))
      { encode (emptyState) with pc := nullLoad.size } 3 := by
  have h : Program.Exec (instructionSet model 0 1 1) nullLoad (emptyState) (emptyState) 2 :=
    Program.Exec.of_eval (fuel := 0) (by rfl)
  simpa using executes_compile h

private def kernel (_ : Unit) (_ _ : ℕ) : ProbComp ℕ :=
  Fin.val <$> ProbComp.unifFin 1

private def drawState (v : ℕ) : Data model 0 1 1 :=
  { emptyState with scalars := Function.update (emptyState).scalars 0 v }

private def chooseBranch : TestCode := .branch (.scalar () 0 0) .skip .skip

private def drawThenBranch : TestCode := .seq (.op (.scalar () 0 0 0)) chooseBranch

private def sampled : ProbComp (Data model 0 1 1 × ℕ) :=
  (fun (k : Fin 2) => (drawState k.val, if k.val = 0 then 2 else 3)) <$> ProbComp.unifFin 1

private theorem exec_drawThenBranch :
    Program.ExecRand (I := instructionSet model 0 1 1) (evalRand kernel)
      drawThenBranch (emptyState) sampled := by
  have hdraw : Program.ExecRand (I := instructionSet model 0 1 1) (evalRand kernel)
      (.op (.scalar () 0 0 0)) (emptyState)
      ((fun (k : Fin 2) => (drawState k.val, 1)) <$> ProbComp.unifFin 1) := by
    simpa only [evalRand, Option.some.injEq, kernel, drawState, Functor.map_map,
      Function.comp_apply] using
      (Program.ExecRand.op (I := instructionSet model 0 1 1) (evalRand := evalRand kernel)
        (o := .scalar () 0 0 0) (x := emptyState) rfl)
  let branchResult (x : Data model 0 1 1) : ProbComp (Data model 0 1 1 × ℕ) :=
    pure (x, if x.scalars 0 = 0 then 1 else 2)
  have hbranch (x : Data model 0 1 1) :
      Program.ExecRand (I := instructionSet model 0 1 1) (evalRand kernel)
        chooseBranch x (branchResult x) := by
    by_cases hx : x.scalars 0 = 0
    · have ht : (instructionSet model 0 1 1).Holds (.scalar () 0 0) x := by
        simp [model, hx]
      simpa [chooseBranch, branchResult, hx] using
        (Program.ExecRand.branch_pos (neg := .skip) ht (Program.ExecRand.skip
          (I := instructionSet model 0 1 1) (evalRand := evalRand kernel) (x := x)))
    · have ht : ¬(instructionSet model 0 1 1).Holds (.scalar () 0 0) x := by
        simp [model, hx]
      simpa [chooseBranch, branchResult, hx] using
        (Program.ExecRand.branch_neg (pos := .skip) ht (Program.ExecRand.skip
          (I := instructionSet model 0 1 1) (evalRand := evalRand kernel) (x := x)))
  have hexec := Program.ExecRand.seq (m₂ := branchResult) hdraw (fun z _ => hbranch z.1)
  have heq :
      (do
        let z₁ ← (fun (k : Fin 2) => (drawState k.val, 1)) <$> ProbComp.unifFin 1
        let z₂ ← branchResult z₁.1
        pure (z₂.1, z₁.2 + z₂.2)) = sampled := by
    simp only [branchResult, pure_bind, sampled, ← bind_pure_comp]
    apply congrArg (fun f => ProbComp.unifFin 1 >>= f)
    funext k
    by_cases hk : k.val = 0 <;> simp [drawState, hk]
  rw [heq] at hexec
  exact hexec

example :
    Program.ExecRand
      (I := PointerMachine.instructionSet model (layout 1 1))
      (PointerMachine.Op.evalRand kernel) (compile drawThenBranch) (encode (emptyState))
      ((fun z => (encode z.1, z.2)) <$> sampled) ∧
    (drawState 0, 2) ∈ sampled.support ∧ (drawState 1, 3) ∈ sampled.support := by
  refine ⟨?_, ?_, ?_⟩
  · exact execRand_compile (M := model) kernel exec_drawThenBranch
  · exact OracleComp.mem_supportWith_map_iff.mpr ⟨0, ProbComp.mem_support_unifFin _ _, rfl⟩
  · exact OracleComp.mem_supportWith_map_iff.mpr ⟨1, ProbComp.mem_support_unifFin _ _, rfl⟩

example :
    PointerMachine.runRand kernel (compile drawThenBranch).program 3 (encode (emptyState)) =
      (fun z => { encode z.1 with pc := drawThenBranch.size }) <$> sampled := by
  have hb : ∀ z ∈ sampled.support, z.2 ≤ 3 := by
    intro z hz
    obtain ⟨_, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    split <;> omega
  simpa using runRand_compile kernel exec_drawThenBranch hb
