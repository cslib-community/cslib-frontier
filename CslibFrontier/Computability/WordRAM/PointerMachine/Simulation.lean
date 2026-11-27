/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Compile
public import CslibFrontier.Computability.WordRAM.PointerMachine.Input

/-! # Standard word-RAM execution on an allocating pointer machine

The concrete compiler replaces memory accesses by the verified AVL dictionary programs.
The time bound is logarithmic in the number of retained dictionary entries; writing zero
retains its node. Each source instruction allocates at most one node. Physical heap pointers
are opaque; source addresses and word operations are scalar data in `model w`.

Only successful deterministic source executions are simulated. The input is the explicit
`inputState` encoding; as for source `Data.init`, constructing that encoding is not charged.
-/

public section
namespace Cslib.WordRAM.PointerMachine
open Cslib.DataStructure
variable {w r : ℕ}

/-- A continuing source run is simulated with logarithmic overhead in the final dictionary
size. The complete register/memory representation is preserved, and both dictionary size
and allocated space grow by at most one per source instruction. -/
theorem runs_compile {p : Program .standard r} {x y : State r} {n : ℕ}
    {s : Cslib.PointerMachine.State (model w) (layout r)}
    {tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)} {avl : AVLTree ℕ}
    (rep : Represents x.data s tree avl) (pc : s.pc = blockSize w r * x.pc)
    (run : Runs w p x y n) :
    ∃ t tree' avl' time, Cslib.PointerMachine.Runs (compile w p) s t time ∧
      Represents y.data t tree' avl' ∧ t.pc = blockSize w r * y.pc ∧
      avl.elements.card ≤ avl'.elements.card ∧ avl'.elements.card ≤ avl.elements.card + n ∧
      time ≤ n * (294 * Nat.log 2 (avl'.elements.card + 1) + 56) ∧
      t.heap.length ≤ s.heap.length + n := by
  induction run with
  | refl => exact ⟨s, tree, avl, 0, .refl _, rep, pc, le_rfl, by omega, by omega, by omega⟩
  | tail x y n steps next ih =>
    obtain ⟨t, tree', avl', time, run, rep', pc', grows, card, bound, space⟩ := ih
    obtain ⟨u, tree'', avl'', cost, last, rep'', pc'', grows', card', bound', space'⟩ :=
      step_compile p x y t tree' avl' rep' pc' next
    have logBound := Nat.log_mono_right (b := 2) (Nat.add_le_add_right grows' 1)
    refine ⟨u, tree'', avl'', time + cost, run.trans last, rep'', pc'',
      grows.trans grows', by omega, ?_, by omega⟩
    calc
      time + cost ≤ n * (294 * Nat.log 2 (avl''.elements.card + 1) + 56) +
          (294 * Nat.log 2 (avl''.elements.card + 1) + 56) :=
        Nat.add_le_add (bound.trans (Nat.mul_le_mul_left n (by omega))) (by omega)
      _ = (n + 1) * (294 * Nat.log 2 (avl''.elements.card + 1) + 56) := by simp [Nat.add_mul]

/-- A successful source execution is compiled to a halting pointer-machine execution with
its returned word in scalar register three. The complete represented final data is retained.
The logarithmic factor uses retained dictionary entries, including cells written back to zero. -/
theorem executes_compile {p : Program .standard r} {x : State r} {v n : ℕ}
    {s : Cslib.PointerMachine.State (model w) (layout r)}
    {tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)} {avl : AVLTree ℕ}
    (rep : Represents x.data s tree avl) (pc : s.pc = blockSize w r * x.pc)
    (execution : Executes w p x v n) :
    ∃ y t tree' avl' time, Cslib.PointerMachine.Executes (compile w p) s t time ∧
      t.data 3 = v ∧ Runs w p x y (n - 1) ∧ step w p y = .halt v ∧
      Represents y.data t tree' avl' ∧
      avl'.elements.card ≤ avl.elements.card + (n - 1) ∧
      time ≤ n * (294 * Nat.log 2 (avl'.elements.card + 1) + 56) ∧
      t.heap.length ≤ s.heap.length + (n - 1) := by
  obtain ⟨y, m, run, halt, rfl⟩ := execution
  obtain ⟨t, tree', avl', time, run', rep', pc', _, card, bound, space⟩ :=
    runs_compile rep pc run
  obtain ⟨u, finish, output, heap, finalRep⟩ :=
    halt_compile p y v t tree' avl' rep' pc' halt
  refine ⟨y, u, tree', avl', time + 2, ?_, output, by simpa using run, halt, finalRep,
    by simpa using card,
    ?_, by simpa [heap] using space⟩
  · obtain ⟨k, last, terminal, cost⟩ := finish
    exact ⟨time + k, run'.trans last, terminal, by omega⟩
  · calc
      time + 2 ≤ m * (294 * Nat.log 2 (avl'.elements.card + 1) + 56) +
          (294 * Nat.log 2 (avl'.elements.card + 1) + 56) := Nat.add_le_add bound (by omega)
      _ = (m + 1) * (294 * Nat.log 2 (avl'.elements.card + 1) + 56) := by simp [Nat.add_mul]

/-- Every successful standard word-RAM run from a list input has an actual pointer-machine
execution returning the same word. For `n` source instructions and `N` input words it uses
at most `N + n` records and `n * (294 * log₂ (N + n + 1) + 56)` instructions, including halt.
Target scalars are unbounded naturals carrying the standard word operations at source width `w`,
together with AVL height operations; this is not a simulation by an atom-only scalar model.
Input encoding is explicitly constructed by `inputState` and is not charged in either model.
This simulates successful deterministic runs, without asserting fault equivalence. -/
theorem executes_input {p : Program .standard r} {input : List ℕ} {v n : ℕ}
    (execution : Executes w p ⟨0, Data.init input⟩ v n) :
    ∃ t time, Cslib.PointerMachine.Executes (compile w p) (inputState w r input) t time ∧
      t.data 3 = v ∧ time ≤ n * (294 * Nat.log 2 (input.length + n + 1) + 56) ∧
      t.heap.length ≤ input.length + n ∧ t.Valid := by
  obtain ⟨y, t, tree, avl, time, run, output, _, _, _, card, bound, space⟩ :=
    executes_compile (inputState_represents w r input) (by simp [inputState]) execution
  have positive := execution.pos
  have initialCard : (inputKeys (input.length + 1)).elements.card = input.length + 1 := by
    rw [elements_inputKeys, Finset.card_range]
  rw [initialCard] at card
  have logBound := Nat.log_mono_right (b := 2)
    (show avl.elements.card + 1 ≤ input.length + n + 1 by omega)
  refine ⟨t, time, run, output, bound.trans (Nat.mul_le_mul_left n (by omega)), ?_,
    run.valid (inputState_valid w r input)⟩
  rw [inputState_heap_length] at space
  omega

end Cslib.WordRAM.PointerMachine
