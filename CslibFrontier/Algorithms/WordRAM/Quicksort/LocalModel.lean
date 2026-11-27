/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
public import CslibFrontier.Computability.WordRAM.Defs

/-!
# Scalar primitives of local-address quicksort

Counters and keys are natural numbers. The randomized interpretation adds one bounded uniform
draw as a unit-cost scalar instruction. A draw with bound `b` yields an index below `b`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM

/-- Scalar operations used by local-address quicksort. -/
inductive LocalScalar where
  | bin (op : BinOp)
  | draw

/-- The scalar basis shared by the local RAM and the pointer machine. -/
@[expose, reducible] def localModel : Cslib.PointerMachine.Model where
  Value := ℕ
  undefined := 0
  Op := LocalScalar
  Test := Unit
  evalOp
    | .bin op, a, b => op.eval a b
    | .draw, _, _ => 0
  evalTest _ a b := decide (a < b)

/-- Arithmetic is deterministic. A draw uses the first operand as its exclusive upper bound
and returns zero for an empty interval. -/
@[expose] def localKernel : LocalScalar → ℕ → ℕ → ProbComp ℕ
  | .bin op, a, b => pure (op.eval a b)
  | .draw, a, _ => Fin.val <$> ProbComp.unifFin (a - 1)

/-- A code fragment whose scalar operations have deterministic meanings under the kernel. -/
@[expose] def NoDraw {p d : ℕ}
    (c : Program.Code (Local.Op localModel p d) (Local.Test localModel p d)) : Prop :=
  ∀ dst a b, Local.Op.scalar (M := localModel) LocalScalar.draw dst a b ∉ c.ops

private theorem op_asRand {n p d : ℕ} {o : Local.Op localModel p d}
    {x y : Local.Data localModel n p d} (ho : Local.Op.eval x o = y)
    (hn : ∀ dst a b, o ≠ .scalar LocalScalar.draw dst a b) :
    Local.evalRand localKernel o x = some (pure y) := by
  subst y
  cases o with
  | scalar op dst a b =>
    cases op with
    | draw => exact (hn dst a b rfl).elim
    | bin => simp [Local.evalRand, localKernel, Local.Op.eval]
  | _ => rfl

/-- A fragment with no draw has the same result and instruction count under the randomized
semantics. -/
theorem exec_asRand {n p d : ℕ}
    {c : Program.Code (Local.Op localModel p d) (Local.Test localModel p d)}
    {x y : Local.Data localModel n p d} {t : ℕ}
    (h : Program.Exec (Local.instructionSet localModel n p d) c x y t) (hn : NoDraw c) :
    Program.ExecRand (I := Local.instructionSet localModel n p d) (Local.evalRand localKernel)
      c x (pure (y, t)) := by
  let I := Local.instructionSet localModel n p d
  let ev := Local.evalRand (M := localModel) (n := n) (p := p) (d := d) localKernel
  refine Program.Exec.rec (I := I)
    (motive := fun c x y t _ => NoDraw c → Program.ExecRand (I := I) ev c x (pure (y, t)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h hn
  · intro _ _
    exact .skip
  · intro o a b he hs
    have hp : ev o a = some (pure b) := op_asRand (Option.some.inj he) fun dst r s heq =>
      hs dst r s (heq.symm ▸ List.mem_singleton_self _)
    simpa only [map_pure] using Program.ExecRand.op (I := I) hp
  · intro _ _ _ _ z _ nt _ _ ih₁ ih₂ hs
    have ha := ih₁ fun dst r s hm => hs dst r s (by simp [hm])
    have hb := ih₂ fun dst r s hm => hs dst r s (by simp [hm])
    simpa only [pure_bind] using Program.ExecRand.seq ha (m₂ := fun _ => pure (z, nt))
      fun _ hz => (OracleComp.eq_of_mem_supportWith_pure hz).symm ▸ hb
  · intro _ _ _ _ _ _ ht _ ih hs
    simpa only [map_pure] using
      Program.ExecRand.branch_pos ht (ih fun dst r s hm => hs dst r s (by simp [hm]))
  · intro _ _ _ _ _ _ ht _ ih hs
    simpa only [map_pure] using
      Program.ExecRand.branch_neg ht (ih fun dst r s hm => hs dst r s (by simp [hm]))
  · intro _ _ _ ht _
    exact .loop_exit ht
  · intro _ _ _ _ z _ nt ht _ _ ih₁ ih₂ hs
    simpa only [pure_bind] using Program.ExecRand.loop_iter ht (ih₁ hs)
      (ml := fun _ => pure (z, nt))
      fun _ hz => (OracleComp.eq_of_mem_supportWith_pure hz).symm ▸ ih₂ hs
  · intro _ _ _ ht _
    exact .loopUntil_exit ht
  · intro _ _ _ _ z _ nt ht _ _ ih₁ ih₂ hs
    simpa only [pure_bind] using Program.ExecRand.loopUntil_iter ht (ih₁ hs)
      (ml := fun _ => pure (z, nt))
      fun _ hz => (OracleComp.eq_of_mem_supportWith_pure hz).symm ▸ ih₂ hs

end Cslib.Algorithms.WordRAM.Quicksort
