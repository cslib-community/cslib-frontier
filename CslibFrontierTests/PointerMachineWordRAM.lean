/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module

import CslibFrontier.Computability.PointerMachine.WordRAM.Correctness
import CslibFrontier.Computability.PointerMachine.WordRAM.Encoding
import Mathlib.Tactic.FinCases

/-!
# Pointer-machine compiler clients

A concrete natural-number scalar basis supplies actual standard word-RAM implementations.
The main client allocates and links nodes, stores and loads data, adds two values, tests scalar
equality and order, and follows pointers to null. Separate examples check empty records and
word overflow.
-/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.PointerMachine.WordRAM
open Cslib.WordRAM (Code ExecWithin)

private inductive Operation where
  | constant (n : ℕ) | add | sub

private inductive Test where
  | eq | lt

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Operation
  Test := Test
  evalOp
    | .constant n, _, _ => n
    | .add, a, b => a + b
    | .sub, a, b => a - b
  evalTest
    | .eq, a, b => decide (a = b)
    | .lt, a, b => decide (a < b)

private def operation {L : Layout} (o : Operation) (d a b : Fin (regCount L)) :
    Code .standard (regCount L) :=
  match o with
  | .constant n => .op (.const d n)
  | .add => .op (.bin .add d a b)
  | .sub => .op (.bin .sub d a b)

private def condition {L : Layout} (p : Test) (a b : Fin (regCount L)) :
    Cslib.WordRAM.Cond (regCount L) :=
  match p with
  | .eq => .eq a b
  | .lt => .lt a b

private theorem set_result {L : Layout} (x : Cslib.WordRAM.Data (regCount L))
    (d : Fin (regCount L)) (v : ℕ) : ScalarResult d v x (x.set d v) where
  result := by simp [Cslib.WordRAM.Data.set]
  memory := rfl
  frame r _ hrd := by simp [Cslib.WordRAM.Data.set, Function.update_of_ne hrd]

private def scalars (L : Layout) : Scalars model L where
  encode := Function.Embedding.refl _
  op := operation
  test p d a b := .branch (condition p a b) (.op (.const d 1)) (.op (.const d 0))
  opTime _ := 1
  testTime _ := 3
  OpSafe _ _ _ _ := True
  TestSafe _ _ _ _ := True
  op_spec w o d a b x u v hu hv _ hfit := by
    change x.regs a = u at hu
    change x.regs b = v at hv
    change Cslib.WordRAM.Fits w (model.evalOp o u v) at hfit
    refine ⟨x.set d (model.evalOp o u v), ?_, set_result ..⟩
    cases o with
    | constant n => exact ExecWithin.const hfit
    | add =>
      simpa [operation, model, hu, hv] using
        (ExecWithin.bin (w := w) (x := x) (f := .add) (d := d) (i := a) (j := b)
          (by simpa [model, hu, hv] using hfit))
    | sub =>
      simpa [operation, model, hu, hv] using
        (ExecWithin.bin (w := w) (x := x) (f := .sub) (d := d) (i := a) (j := b)
          (by simpa [model, hu, hv] using hfit))
  test_spec w p d a b x u v hu hv _ hwidth := by
    change x.regs a = u at hu
    change x.regs b = v at hv
    refine ⟨x.set d (if model.evalTest p u v then 1 else 0), ?_, set_result ..⟩
    have heq : (condition p a b).Holds x ↔ model.evalTest p u v = true := by
      cases p <;> simp [condition, Cslib.WordRAM.Cond.holds_eq,
        Cslib.WordRAM.Cond.holds_lt, hu, hv]
    cases hb : model.evalTest p u v with
    | true =>
      have hc := heq.mpr hb
      have he : ExecWithin (B := .standard) w
          (.branch (condition p a b) (.op (.const d 1)) (.op (.const d 0)))
          x (x.set d 1) 3 :=
        ((ExecWithin.const (d := d) (x := x) hwidth).branch_pos hc).mono (by decide)
      simpa only [hb, ite_true] using he
    | false =>
      have hc : ¬(condition p a b).Holds x := by
        intro hc
        have ht := heq.mp hc
        rw [hb] at ht
        contradiction
      have he : ExecWithin (B := .standard) w
          (.branch (condition p a b) (.op (.const d 1)) (.op (.const d 0)))
          x (x.set d 0) 3 :=
        (ExecWithin.const (d := d) (x := x) (Cslib.WordRAM.fits_zero w)).branch_neg hc
      simpa only [hb, Bool.false_eq_true, ite_false] using he


private abbrev layout : Layout := ⟨2, 2, 1, 1⟩
private abbrev S := State model layout
private def initial : S := State.empty

private def sampleCode : List (Instr model layout) :=
  [.create 0, .create 1, .storePtr 0 0 1, .op (.constant 3) 0 0 0,
   .storeData 0 1 0, .loadData 1 0 1, .op .add 0 0 1,
   .ifTest .eq 1 1 9, .goto 99, .ifTest .lt 1 0 11, .goto 99, .null 1,
   .ifPtrEq 0 1 15, .loadPtr 0 0 0, .goto 12, .halt]

private def state : ℕ → S
  | 0 => initial
  | n + 1 => (step sampleCode (state n)).getD (state n)

private theorem transition (n : Fin 17) : step sampleCode (state n) = some (state (n + 1)) := by
  fin_cases n <;> rfl

private theorem run (n : ℕ) (hn : n ≤ 17) : Runs sampleCode initial (state n) n := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact .tail _ _ _ _ (ih (by omega)) (transition ⟨n, by omega⟩)

private theorem execution : Executes sampleCode initial (state 17) 18 :=
  ⟨17, run 17 le_rfl, rfl, rfl⟩

private theorem traceFits (n : Fin 18) : Fits (scalars layout).encode 4 (state n) := by
  fin_cases n <;> constructor <;> decide

example : (state 17).data 0 = 6 ∧ (state 17).data 1 = 3 ∧ (state 17).ptr 0 = none :=
  ⟨rfl, rfl, rfl⟩

-- The actual compiler transfers the complete state, with a concrete target instruction bound.
example : ∃ z k, k + 1 ≤ 252 ∧
    Cslib.WordRAM.Runs 4 ((scalars layout).compile sampleCode)
      ⟨0, encodeState (scalars layout).encode initial⟩
      ⟨(scalars layout).blockSize sampleCode * 15, z⟩ k ∧
    z.regs (dataReg layout 0) = 6 ∧
    Cslib.WordRAM.step 4 ((scalars layout).compile sampleCode)
      ⟨(scalars layout).blockSize sampleCode * 15, z⟩ = .halt 0 := by
  obtain ⟨z, k, hk, hr, hz, hh⟩ := (scalars layout).executes_compile
    State.empty_valid execution
    (fun z m hm htime => by
      cases hm.deterministic (run m (by omega))
      exact traceFits ⟨m, htime⟩)
    (fun _ _ _ _ i _ => by cases i <;> trivial)
  exact ⟨z, k, hk, hr, hz.data 0, hh⟩

-- Even a fieldless record has an address and advances the allocation pointer.
private abbrev emptyLayout : Layout := ⟨1, 0, 0, 0⟩
private def emptyInput : State model emptyLayout := State.empty

example : ∃ z, ExecWithin 2 ((scalars emptyLayout).effect (.create 0))
      (encodeState (scalars emptyLayout).encode emptyInput) z 4 ∧
    Repr (scalars emptyLayout).encode ((Instr.create 0).effect emptyInput) z :=
  (scalars emptyLayout).create_spec 0 (repr_encodeState _ _) (by
    constructor <;> simp [Instr.effect, emptyInput, State.empty, Record.blank, scalars, model,
      nodeAddr, stride, emptyLayout, Cslib.WordRAM.Fits])

-- One bit cannot hold the post-allocation next-free address. The emitted sampleCode really faults.
example : ((scalars emptyLayout).effect (.create 0)).eval 1 0
    (encodeState (scalars emptyLayout).encode emptyInput) = none := rfl

-- Source natural arithmetic is unbounded; the compiler requires fitting results.
example : ((scalars layout).effect (.op (.constant 16) 0 0 0)).eval 4 0
    (encodeState (scalars layout).encode initial) = none := rfl
