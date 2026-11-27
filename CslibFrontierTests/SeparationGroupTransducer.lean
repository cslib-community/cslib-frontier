/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Transducer
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed

/-! Tests of the generic layer of the group program, as a client:

* programs on lists with constantly many entries: an entry, a list of values, a case distinction
  by a number;
* a rule for typed values: a guessed number, held as a tree, is increased;
* a transducer that copies its input list to its output list: one step of a run, the formula that
  runs it, and the lengths of its output. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.SeparationGroupTransducer

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree
  Cslib.Circuits.Arithmetic.Separation.GroupProgram

variable {A : Type} [CommRing A] (θ : List Bool → A)

/-! ### Programs on lists -/

/-- The entry at position `1` of a quoted list, in three steps. -/
example (a b c x : Tree) : Gives θ (nthF 1 (.quote (listT [a, b, c]))) x b 3 :=
  nthF_gives 1 (Gives.quote _ x)

/-- The list of two copies of the argument. -/
example (x : Tree) : Gives θ (listF (List.ofFn fun _ : Fin 2 => .id)) x
    (listT (List.ofFn fun _ : Fin 2 => x)) (2 * (1 + 1) + 1) :=
  listF_gives fun _ => Gives.id x

/-- At the number `1`, a switch goes on with its second formula. -/
example (a b c : Tree) : Gives θ (switchF .id [.quote a, .quote b, .quote c]) (num 1) b 8 :=
  (switchF_does (Gives.id (num 1)) (j := 1) rfl (Gives.quote b _)).mono (by decide)

/-! ### Typed values -/

/-- Guess `1` or `2`, as trees. -/
theorem guess_does (x : Tree) : Does θ (.ite .guess (.quote (num 1)) (.quote (num 2))) x
    (([(1, 1), (1, 2)] : List (A × ℕ)).map (Prod.map id num)) 3 :=
  Does.either (Gives.quote _ x) (Gives.quote _ x)

/-- The successor of a number, on its tree. -/
theorem succ_gives (n : ℕ) : Gives θ (.cons (.quote .nil) .id) (num n) (num (n + 1)) 3 :=
  (Gives.quote .nil _).cons (Gives.id _)

/-- A guessed number is increased: the list of typed values is computed in `ℕ`. -/
example (x : Tree) :
    Does θ (lett (.ite .guess (.quote (num 1)) (.quote (num 2))) (.cons (.quote .nil) .id)) x
      (([(1, 2), (1, 3)] : List (A × ℕ)).map (Prod.map id num)) 8 :=
  (Does.lett_enc_enc (f := fun n => [(1, n + 1)]) (guess_does θ x)
    fun b _ => succ_gives θ b.2).of_eq (by simp [List.weightedBind])

/-! ### A transducer -/

/-- One control, one input list and one output list of bits: push the bit that is read. -/
def copy : Fin 1 → (Fin 1 → Bool) → List (Transducer.Choice 1 1 Bool) :=
  fun _ v => [⟨.one, 0, fun _ => [v 0]⟩]

/-- The state with the control `0`, one input list and one output list. -/
def st (i o : List Bool) : Transducer.State 1 1 1 Bool := ⟨0, fun _ => i, fun _ => o⟩

/-- One step moves the first bit of the input to the output. -/
theorem run_one (b : Bool) (i o : List Bool) :
    Transducer.run θ copy 1 (st (b :: i) o) = [(1, st i (b :: o))] := by
  simp [Transducer.run_succ, Transducer.run_zero, Transducer.step, Transducer.Choice.apply, copy,
    st, WE.val, List.weightedBind]

/-- A formula computes the step, on the encodings of the states. -/
example (b : Bool) (i o : List Bool) : ∃ F c,
    Does θ F (.cons (num 1) ((st (b :: i) o).enc bit)) [(1, (st i (b :: o)).enc bit)] c := by
  obtain ⟨F, κ, h⟩ := Transducer.exists_formula_run (θ := θ) bit copy
  exact ⟨F, _, (h 1 (st (b :: i) o)).of_eq (by rw [run_one]; rfl)⟩

/-- Every step pushes one bit. -/
example (k : ℕ) (i : List Bool) : ∀ q ∈ Transducer.run θ copy k (st i []),
    (q.2.outputs 0).length = k := by
  simpa [st] using Transducer.mem_run_induction (θ := θ) (tab := copy)
    (Inv := fun m s => (s.outputs 0).length = m) (m := 0) (s := st i []) (k := k)
    (fun s m hm q hq => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hq
      obtain rfl := List.mem_singleton.1 ho
      simpa [Transducer.Choice.apply] using hm) rfl

end CslibFrontierTests.SeparationGroupTransducer
