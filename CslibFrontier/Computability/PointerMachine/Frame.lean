/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Basic

/-!
# Scalar-field frames from program syntax

A program which neither allocates nor stores a particular scalar field preserves that
field at every heap address. This applies even while pointer fields are rewired, so
tree-balancing programs can preserve dictionary payloads without repeating heap-update proofs.
-/

public section
namespace Cslib.PointerMachine
variable {M : Model} {L : Layout}

/-- Whether an instruction may write field `f` at some heap address.
Allocation counts as a write because it initializes a new record. -/
@[expose] def Instr.WritesData (i : Instr M L) (f : Fin L.dataFields) : Prop :=
  match i with
  | .create _ => True
  | .storeData g _ _ => g = f
  | _ => False

/-- An instruction that neither allocates nor stores `f` preserves that field at every
address. -/
theorem Instr.effect_data_frame (i : Instr M L) (f : Fin L.dataFields)
    (safe : ¬ i.WritesData f) (s : State M L) (a : ℕ) :
    ((i.effect s).heap[a]?).map (fun r => r.data f) =
      (s.heap[a]?).map (fun r => r.data f) := by
  have hmod (base : Fin L.ptrRegs) (g : Record M L → Record M L)
      (hg : ∀ r, (g r).data f = r.data f) :
      ((s.modify base g).heap[a]?).map (fun r => r.data f) =
        (s.heap[a]?).map (fun r => r.data f) := by
    rcases p : s.ptr base with _ | b
    · simp [State.modify, p]
    · by_cases same : b = a <;> simp [State.modify, p, same, Option.map_map, Function.comp_def, hg]
  cases i <;> simp only [Instr.effect, Instr.WritesData] at safe ⊢
  case create => exact (safe trivial).elim
  case loadPtr _ _ base | loadData _ _ base => cases s.deref base <;> rfl
  case storePtr _ base _ => exact hmod base _ fun _ => rfl
  case storeData _ base _ => exact hmod base _ fun _ => Function.update_of_ne (Ne.symm safe) _ _
  all_goals rfl

/-- When the program has no allocation or store to `field`, every run preserves the
scalar field at every address, including absence of a record. Pointer writes are unrestricted. -/
theorem Runs.data_frame {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (run : Runs code x y n) (field : Fin L.dataFields)
    (safe : ∀ i ∈ code, ¬ i.WritesData field) (a : ℕ) :
    (y.heap[a]?).map (fun r => r.data field) = (x.heap[a]?).map (fun r => r.data field) := by
  induction run with
  | refl => rfl
  | tail s t n _ next ih =>
    obtain ⟨i, fetch, _, rfl⟩ := step_eq_some_iff.mp next
    exact (Instr.effect_data_frame i field (safe i (List.mem_of_getElem? fetch)) s a).trans ih

end Cslib.PointerMachine
