/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Insert
public import CslibFrontier.Computability.PointerMachine.WordRAM.NaturalSimulation

/-!
# AVL insertion by a standard word-RAM program

The linked pointer-machine implementation of Frontier's AVL insertion compiles to ordinary
word-RAM instructions using the certified natural scalar basis. The resulting finite program
has logarithmic instruction cost and allocates at most one node. All nonheight payloads survive.

The input is an encoded linked AVL tree, with natural keys and scalar fields. The caller supplies
a bound on its initial scalar values and enough word width for that bound plus the source
instruction budget and a conservative allocation budget. Intermediate fit and scalar-operation
correctness are proved, not supplied by the caller. Encoding the initial heap is not charged.
-/

public section
namespace Cslib.DataStructure.AVLTree.WordRAM
open Cslib.PointerMachine SearchTree.PointerMachine
open Cslib.PointerMachine.WordRAM (nodeAddr regCount Repr encodeState)
open Cslib.PointerMachine.WordRAM.Natural (model scalars)
variable {extra regs : ℕ}

/-- A concrete standard word-RAM program implements AVL insertion with logarithmic time.
Its final represented state has exactly the functional insertion's keys and caches, preserves
old payloads, and allocates at most one node. Width requirements concern only the initial data
bound and explicit instruction budget; input encoding is outside the charged run. -/
theorem insert_correct {w b : ℕ} (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (source : Fin (extra + 1) → Fin (regs + 3))
    (safe : ∀ f, f ≠ field → f ≠ 0 → source f ≠ 1 ∧ source f ≠ 2)
    (s : State model (layout extra (regs + 1)))
    (tree : BinaryTree (Label model extra)) (original : AVLTree ℕ)
    (stateValid : s.Valid) (initial : s.DataValid (· ≤ b))
    (rep : Represents s.heap none tree) (distinct : AddressesDistinct tree)
    (matched : PointerMachine.Matches id field tree original) (valid : original.Valid)
    (cursor : s.ptr 0 = root tree) (rootReg : s.ptr 1 = root tree) (pc : s.pc = 0) :
    let limit := 282 * Nat.log 2 (original.elements.card + 1) + extra + 31
    let code := PointerMachine.insert (M := model) .zero .maxSucc .lt .heavy .le field source
    let S := scalars (layout extra (regs + 1))
    Cslib.WordRAM.Fits w (nodeAddr (layout extra (regs + 1)) (s.heap.length + limit)) →
    Cslib.WordRAM.Fits w (b + limit) →
    ∃ (t : State model (layout extra (regs + 1))) (result : BinaryTree (Label model extra))
      (z : Cslib.WordRAM.Data (regCount (layout extra (regs + 1)))) (k : ℕ),
      PointerMachine.InsertResult id field source s t tree result original ∧
      k + 1 ≤ (4 * extra + 22) * limit ∧
      Cslib.WordRAM.Runs w (S.compile code) ⟨0, encodeState S.encode s⟩
        ⟨S.blockSize code * t.pc, z⟩ k ∧ Repr S.encode t z ∧
      Cslib.WordRAM.step w (S.compile code) ⟨S.blockSize code * t.pc, z⟩ = .halt 0 := by
  intro limit code S memory values
  obtain ⟨t, result, time, run, _, bound, outcome⟩ :=
    PointerMachine.insert_correct (M := model) .zero .maxSucc .lt .heavy .le id
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) field notKey source safe s tree original
      rep distinct matched valid cursor rootReg pc
  obtain ⟨z, k, cost, execution, representation, halt⟩ :=
    Cslib.PointerMachine.WordRAM.Natural.executes_compile stateValid run bound initial memory values
  have overhead : S.overhead code ≤ 4 * extra + 22 := by
    have h := Cslib.PointerMachine.WordRAM.Natural.overhead_le code
    change S.overhead code ≤ max 7 (4 * (3 + (extra + 1)) + 6) at h
    omega
  refine ⟨t, result, z, k, outcome, cost.trans (Nat.mul_le_mul overhead bound), ?_,
    representation, halt⟩
  simpa only [pc, Nat.mul_zero] using execution

end Cslib.DataStructure.AVLTree.WordRAM
