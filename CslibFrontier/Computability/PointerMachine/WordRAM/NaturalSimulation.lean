/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Natural
public import CslibFrontier.Computability.PointerMachine.WordRAM.Correctness
public import CslibFrontier.Computability.PointerMachine.Data

/-!
# Compiling bounded natural-scalar computations

For the natural scalar basis, one source instruction increases the largest scalar by at most
one and allocates at most one record. An initial scalar bound and an instruction bound therefore
supply a sufficient word width for the complete execution. `executes_compile` discharges all
intermediate word-fit and scalar-admissibility premises of the general compiler.

The target begins with the canonical encoded input; input preparation is not charged.
The bounds are conservative: a particular algorithm may need much less scalar headroom.
-/

public section
namespace Cslib.PointerMachine.WordRAM.Natural
variable {L : Layout}

private theorem runs_data_le {code : List (Instr model L)} {x y : State model L} {n b : ℕ}
    (run : Runs code x y n) (initial : x.DataValid (· ≤ b)) : y.DataValid (· ≤ b + n) := by
  induction run with
  | refl => simpa only [Nat.add_zero] using initial
  | tail s _ n _ next ih =>
    obtain ⟨i, _, _, rfl⟩ := step_eq_some_iff.mp next
    simpa only [State.DataValid, Nat.add_assoc] using
      Instr.effect_dataValid_of (M := model) (i := i) (x := s)
        (P := fun a : ℕ => a ≤ b + n) (Q := fun a : ℕ => a ≤ b + n + 1)
        (fun _ => Nat.le_succ_of_le) (Nat.zero_le _)
        (fun op _ _ ha hc => by
          cases op
          exacts [Nat.zero_le _, Nat.add_le_add_right (max_le ha hc) 1]) ih

/-- The natural basis has a uniform compiler overhead depending only on the record layout,
not on the source program's length or control flow. -/
theorem overhead_le (code : List (Instr model L)) :
    (scalars L).overhead code ≤ max 7 (4 * (L.ptrFields + L.dataFields) + 6) := by
  induction code with
  | nil => simp [Scalars.overhead]
  | cons i code ih =>
    change max ((scalars L).effectTime i + 2) ((scalars L).overhead code) ≤ _
    refine max_le ?_ ih
    cases i <;> simp only [Scalars.effectTime, scalars]
    case op op _ _ _ => cases op <;> simp
    case ifTest test _ _ _ => cases test <;> simp
    all_goals omega

/-- Allocation-free natural-basis programs cost at most seven word-RAM instructions per
source instruction, regardless of the record layout. -/
theorem overhead_le_of_no_create (code : List (Instr model L))
    (h : ∀ r, Instr.create r ∉ code) : (scalars L).overhead code ≤ 7 := by
  induction code with
  | nil => simp [Scalars.overhead]
  | cons i code ih =>
    change max ((scalars L).effectTime i + 2) ((scalars L).overhead code) ≤ _
    refine max_le ?_ (ih fun r hr => h r (List.mem_cons_of_mem i hr))
    cases i <;> simp only [Scalars.effectTime, scalars]
    case create r => exact (h r (List.mem_cons_self ..)).elim
    case op op _ _ _ => cases op <;> decide
    case ifTest test _ _ _ => cases test <;> decide
    all_goals decide

/-- Compile a natural-scalar execution with explicit sufficient width. All initial data is
at most `b`; at most `limit` instructions execute. Fitting `b + limit` and the next-free address
after `limit` allocations suffices, with no hypotheses about intermediate machine states.
The produced target run includes the general compiler's halt and constant time overhead. -/
theorem executes_compile {w time limit b : ℕ} {code : List (Instr model L)}
    {x x' : State model L} (valid : x.Valid) (run : Executes code x x' time)
    (bound : time ≤ limit) (initial : x.DataValid (· ≤ b))
    (memory : Cslib.WordRAM.Fits w (nodeAddr L (x.heap.length + limit)))
    (values : Cslib.WordRAM.Fits w (b + limit)) :
    ∃ z k, k + 1 ≤ (scalars L).overhead code * time ∧
      Cslib.WordRAM.Runs w ((scalars L).compile code)
        ⟨(scalars L).blockSize code * x.pc, encodeState (scalars L).encode x⟩
        ⟨(scalars L).blockSize code * x'.pc, z⟩ k ∧ Repr (scalars L).encode x' z ∧
      Cslib.WordRAM.step w ((scalars L).compile code)
        ⟨(scalars L).blockSize code * x'.pc, z⟩ = .halt 0 := by
  refine (scalars L).executes_compile valid run (fun _ m trace hm => ?_)
    fun _ m trace hm i _ => ?_
  · have data := runs_data_le trace initial
    exact ⟨memory.of_le (Nat.add_le_add_left
        (Nat.mul_le_mul_left (stride L) (trace.length_le.trans (Nat.add_le_add_left (by omega) _)))
        1),
      fun i => values.of_le ((data.1 i).trans (Nat.add_le_add_left (by omega) _)),
      fun node hn f => values.of_le ((data.2 node hn f).trans (Nat.add_le_add_left (by omega) _))⟩
  · cases i <;> simp only [Scalars.Safe, scalars]
    case ifTest test a _ _ _ =>
      cases test
      · trivial
      · trivial
      · exact values.of_le ((Nat.sub_le _ _).trans
          (((runs_data_le trace initial).1 a).trans (Nat.add_le_add_left (by omega) _)))

end Cslib.PointerMachine.WordRAM.Natural
