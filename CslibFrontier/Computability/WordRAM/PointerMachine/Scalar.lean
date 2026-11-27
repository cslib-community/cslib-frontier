/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Defs

/-! # Scalar instruction lowering

Every register-only standard word-RAM operation lowers to one pointer-machine scalar
instruction. The proof preserves source register values and every dictionary scratch register,
heap record and pointer register. Successful source evaluation supplies the overflow premise;
the target has no scalar word-width restriction.
-/

public section
namespace Cslib.WordRAM.PointerMachine
variable {w r : ℕ}

/-- Lower a register-only source operation; memory operations are handled by the dictionary. -/
@[expose] def scalar : Op .standard r → Option (Cslib.PointerMachine.Instr (model w) (layout r))
  | .const d n => some (.op (.constant n) (register d) 0 0)
  | .copy d s => some (.moveData (register d) (register s))
  | .alu (.bin f) d args => some (.op (.bin f) (register d)
      (register (args (0 : Fin 2))) (register (args (1 : Fin 2))))
  | .alu .width d _ => some (.op .width (register d) 0 0)
  | .load .. | .store .. => none

private theorem set_registers (x : Data r) (s : Cslib.PointerMachine.State (model w) (layout r))
    (same : ∀ j, s.data (register j) = x.regs j) (d : Fin r) (v : ℕ) :
    (∀ j, (s.setData (register d) v).data (register j) = (x.set d v).regs j) ∧
    (∀ j, j.val < 4 → (s.setData (register d) v).data j = s.data j) := by
  constructor
  · intro j
    by_cases eq : j = d
    · subst j; simp [Cslib.PointerMachine.State.setData, Data.set]
    · have ne : register j ≠ register d := fun h => eq (register_injective h)
      simp [Cslib.PointerMachine.State.setData, Data.set, eq, ne, same]
  · intro j hj
    have ne : j ≠ register d := by
      intro eq
      have := register_ge_four d
      subst j
      omega
    simp [Cslib.PointerMachine.State.setData, ne]

/-- Successful scalar source evaluation has the same register effect after lowering.
All four dictionary scratch scalars and the entire pointer heap are preserved. -/
theorem scalar_correct (o : Op .standard r) (i : Cslib.PointerMachine.Instr (model w) (layout r))
    (x y : Data r) (s : Cslib.PointerMachine.State (model w) (layout r))
    (same : ∀ j, s.data (register j) = x.regs j)
    (lowered : scalar o = some i) (evaluated : o.eval w x = some y) :
    (∀ j, (i.effect s).data (register j) = y.regs j) ∧
    (∀ j, j.val < 4 → (i.effect s).data j = s.data j) ∧
    (i.effect s).heap = s.heap ∧ (i.effect s).ptr = s.ptr := by
  cases o with
  | const d n =>
    cases Option.some.inj lowered
    obtain ⟨_, rfl⟩ := Data.put_eq_some.mp evaluated
    exact ⟨(set_registers x s same d n).1, (set_registers x s same d n).2, rfl, rfl⟩
  | copy d src =>
    cases Option.some.inj lowered
    cases Option.some.inj evaluated
    simp only [Cslib.PointerMachine.Instr.effect, same]
    exact
      And.intro (set_registers x s same d (x.regs src)).1
        (And.intro (set_registers x s same d (x.regs src)).2 (And.intro rfl rfl))
  | alu f d args =>
    cases f with
    | bin f =>
      change Fin 2 → Fin r at args
      cases Option.some.inj lowered
      have ev : x.put w d (f.eval (x.regs (args 0)) (x.regs (args 1))) = some y := evaluated
      obtain ⟨_, rfl⟩ := Data.put_eq_some.mp ev
      simp only [Cslib.PointerMachine.Instr.effect, model, same]
      have frame := set_registers x s same d (f.eval (x.regs (args 0)) (x.regs (args 1)))
      exact ⟨frame.1, frame.2, rfl, rfl⟩
    | width =>
      have ev : x.put w d w = some y := evaluated
      cases Option.some.inj lowered
      obtain ⟨_, rfl⟩ := Data.put_eq_some.mp ev
      exact ⟨(set_registers x s same d w).1, (set_registers x s same d w).2, rfl, rfl⟩
  | load d a => cases lowered
  | store a src => cases lowered

end Cslib.WordRAM.PointerMachine
