/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
public import CslibFrontier.Algorithms.WordRAM.Quicksort.LocalModel

/-!
# Quicksort pivot selection on linked RAM cells

Given a sampled rank in a nonempty range, the cursor starts at the range's beginning, advances
once per unit of rank and reads the key. The linked implementation is obtained by compiling
the local-address RAM program. A rank of `k` costs at most `4 * k + 3` instructions in the
structured program, including the final payload read.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM
open Local (compile encode instructionSet)

private abbrev pivotModel := localModel

private abbrev PivotCode (p d : ℕ) := Program.Code (Local.Op pivotModel p d)
  (Local.Test pivotModel p d)

private def countdown {p d : ℕ} (cursor : Fin p) (offset zero one : Fin d) : PivotCode p d :=
  .loop (.scalar () zero offset)
    (.seq (.op (.move .next cursor cursor)) (.op (.scalar (.bin .sub) offset offset one)))

/-- Walk from the held cursor by the sampled offset, then read the key. -/
def pivotWalk {p d : ℕ} (cursor : Fin p) (offset zero one dst : Fin d) :
    Program.Code (Local.Op localModel p d)
      (Local.Test localModel p d) :=
  .seq (countdown cursor offset zero one) (.op (.loadData dst cursor))

/-- The walk uses only deterministic primitives. -/
theorem pivotWalk_noDraw {p d : ℕ} (cursor : Fin p) (offset zero one dst : Fin d) :
    NoDraw (pivotWalk cursor offset zero one dst) := by
  simp [NoDraw, pivotWalk, countdown]

private theorem pivotLoop {n p d : ℕ} (cursor : Fin p) (offset zero one : Fin d)
    (hzoff : zero ≠ offset) (hooff : one ≠ offset)
    (x : Local.Data pivotModel n p d) (a : Fin n) (k : ℕ)
    (ha : x.addr cursor = some a) (hk : x.scalars offset = k)
    (hz : x.scalars zero = 0) (ho : x.scalars one = 1) (hfit : a.val + k < n) :
    Program.ExecWithin (instructionSet pivotModel n p d) (countdown cursor offset zero one) x
      { x with
        addr := Function.update x.addr cursor (some ⟨a.val + k, hfit⟩)
        scalars := Function.update x.scalars offset 0 } (4 * k + 2) := by
  induction k generalizing x a with
  | zero =>
    have hstate :
        { x with
          addr := Function.update x.addr cursor (some ⟨a.val + 0, hfit⟩)
          scalars := Function.update x.scalars offset 0 } = x := by
      simp only [Nat.add_zero]
      change ({ x with
        addr := Function.update x.addr cursor (some a)
        scalars := Function.update x.scalars offset 0 } : Local.Data pivotModel n p d) = x
      rw [← ha, ← hk, Function.update_eq_self, Function.update_eq_self]
    rw [hstate]
    exact Program.ExecWithin.loop_exit (by simp [hk, hz])
  | succ k ih =>
    have hnext : a.val + 1 < n := by omega
    let b : Fin n := ⟨a.val + 1, hnext⟩
    let x₁ := (Local.Op.move .next cursor cursor).eval x
    let x₂ := (Local.Op.scalar (LocalScalar.bin .sub) offset offset one).eval x₁
    have haddr : x₂.addr cursor = some b := by
      simp [x₂, x₁, Local.Op.eval, Local.Direction.move, ha, hnext, b]
    have hscalar : x₂.scalars offset = k := by
      simp [x₂, x₁, Local.Op.eval, ha, hk, ho, Cslib.WordRAM.BinOp.eval]
    have hzero : x₂.scalars zero = 0 := by
      simpa [x₂, x₁, Local.Op.eval, ha, hzoff] using hz
    have hone : x₂.scalars one = 1 := by
      simpa [x₂, x₁, Local.Op.eval, ha, hooff] using ho
    have hrest := ih x₂ b haddr hscalar hzero hone (by dsimp [b]; omega)
    have hstep : Program.Exec (instructionSet pivotModel n p d)
        (.seq (.op (.move .next cursor cursor)) (.op (.scalar (.bin .sub) offset offset one)))
        x x₂ 2 := .seq (.op rfl) (.op rfl)
    have hcond : (instructionSet pivotModel n p d).Holds (.scalar () zero offset) x := by
      simp [hz, hk]
    have hrun := (Program.ExecWithin.loop_iter hcond ⟨2, le_rfl, hstep⟩ hrest).mono
      (show 2 + (4 * k + 2) + 2 ≤ 4 * (k + 1) + 2 by omega)
    simpa [countdown, x₂, x₁, Local.Op.eval, Local.Direction.move, ha, hnext, b,
      Function.update_idem, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun

/-- In the local-address RAM, a pivot walk changes only the cursor, rank and output registers. -/
theorem pivotWalk_exec {n p d : ℕ} (cursor : Fin p) (offset zero one dst : Fin d)
    (hzoff : zero ≠ offset) (hooff : one ≠ offset)
    (x : Local.Data localModel n p d)
    (start : Fin n) (rank : ℕ) (haddr : x.addr cursor = some start)
    (hoffset : x.scalars offset = rank)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) (hfit : start.val + rank < n) :
    let a : Fin n := ⟨start.val + rank, hfit⟩
    Program.ExecWithin (instructionSet localModel n p d)
      (pivotWalk cursor offset zero one dst) x
      { x with
        addr := Function.update x.addr cursor (some a)
        scalars := Function.update (Function.update x.scalars offset 0) dst (x.values a) }
      (4 * rank + 3) := by
  intro a
  let z := { x with
    addr := Function.update x.addr cursor (some a)
    scalars := Function.update x.scalars offset 0 }
  have hz : Program.ExecWithin (instructionSet pivotModel n p d)
      (countdown cursor offset zero one) x z (4 * rank + 2) :=
    pivotLoop cursor offset zero one hzoff hooff x start rank haddr hoffset hzero hone hfit
  let y := (Local.Op.loadData dst cursor).eval z
  have hread : Program.Exec (instructionSet pivotModel n p d)
      (.op (.loadData dst cursor)) z y 1 := .op rfl
  have hrun := Program.ExecWithin.seq hz ⟨1, le_rfl, hread⟩
  simpa [pivotWalk, y, z, Local.Op.eval, Nat.add_assoc] using hrun

/-- A compiled countdown walk reads the key at the sampled rank without address arithmetic. -/
theorem pointerPivot_exec {n p d : ℕ} (cursor : Fin p) (offset zero one dst : Fin d)
    (hzoff : zero ≠ offset) (hooff : one ≠ offset)
    (x : Local.Data localModel n p d)
    (start : Fin n) (rank : ℕ) (haddr : x.addr cursor = some start)
    (hoffset : x.scalars offset = rank)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) (hfit : start.val + rank < n) :
    ∃ y, Cslib.PointerMachine.ExecWithin (compile (pivotWalk cursor offset zero one dst))
      (encode x) y (4 * rank + 3) ∧ y.data dst = x.values ⟨start.val + rank, hfit⟩ := by
  obtain ⟨t, ht, h⟩ :=
    pivotWalk_exec cursor offset zero one dst hzoff hooff x start rank haddr hoffset hzero hone hfit
  exact ⟨_, ⟨t, ht, Local.exec_compile h⟩, by simp⟩

end Cslib.Algorithms.WordRAM.Quicksort
