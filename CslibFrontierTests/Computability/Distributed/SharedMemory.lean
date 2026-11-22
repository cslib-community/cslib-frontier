/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.SharedMemory.Hierarchy
import CslibFrontier.Computability.Distributed.SharedMemory.Universal
import Mathlib.Algebra.Group.Nat.Defs

/-! Wait-free shared-memory consensus hierarchy (`1 < 2 < ∞`) and Herlihy's universal construction
(checked as a `module` client with ordinary imports):
* exhaustive `decide`-checked runs of 2-process `testAndSetProtocol` across all 20 six-step
  interleavings and all 4 binary input vectors, plus crash/solo runs and a concrete 3-process
  split-brain failure trace witnessing why `TestAndSet` fails at `n = 3`;
* `decide`-checked runs of `casConsensusProtocol` on `Fin 5` over `Fin 5` proposals;
* concrete `decide`-checked non-commuting/non-overwriting witness on `casObj (none : Option Bool)`
  contrasted with `testAndSetObj`, `swapObj`, and `fetchAndAddObj`;
* `decide`-checked universal construction log replay for both a concurrent bank account with
  overdraft protection and a concurrent FIFO queue, together with proved `ValidSlotSchedule`
  witnesses exercising `universalInvoke_linearizable_of_validSlotSchedule` and
  `universalInvoke_slotIdx_bijective_of_validSlotSchedule`;
* instantiations of the `≤ 1`, `≤ 2`, and `∀ n` consensus-hierarchy theorems. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.SharedMemory

open Cslib Cslib.Distributed.SharedMemory

/-! ### 1. Exhaustive 2-process `TestAndSet` consensus under all interleavings -/

/-- Structural helper generating all interleavings of `a` steps by process `0` and `b` steps by
process `1` on `Fin 2` given fuel `a + b` (structural recursion so `decide` reduces in the
kernel). -/
def interleavingsFuel : ℕ → ℕ → ℕ → List (List (Fin 2))
  | 0, _, _ => [[]]
  | _ + 1, 0, 0 => [[]]
  | fuel + 1, a + 1, 0 => (interleavingsFuel fuel a 0).map (0 :: ·)
  | fuel + 1, 0, b + 1 => (interleavingsFuel fuel 0 b).map (1 :: ·)
  | fuel + 1, a + 1, b + 1 =>
    (interleavingsFuel fuel a (b + 1)).map (0 :: ·) ++
      (interleavingsFuel fuel (a + 1) b).map (1 :: ·)

/-- All interleavings of `a` steps by process `0` and `b` steps by process `1` on `Fin 2`. -/
def interleavings (a b : ℕ) : List (List (Fin 2)) :=
  interleavingsFuel (a + b) a b

theorem interleavings_three_three_length : (interleavings 3 3).length = 20 := by
  decide

/-- Executable 2-process `TestAndSet` consensus protocol on `Fin 2`. -/
def tasProtoFin2 : Protocol (Fin 2) (tasObjFamily (Fin 2) false) (TASState (Fin 2) Bool) Bool :=
  testAndSetProtocol id false (fun p => 1 - p)

/-- Check that running `tasProtoFin2` on `sched` from `inp` drives both processes to decide the
same valid input value. -/
def checkTASRun (inp : Fin 2 → Bool) (sched : List (Fin 2)) : Bool :=
  let c := tasProtoFin2.run sched (tasProtoFin2.initConfig inp)
  match (c.proc 0).decided, (c.proc 1).decided with
  | some d₀, some d₁ => (d₀ == d₁) && ((d₀ == inp 0) || (d₀ == inp 1))
  | _, _ => false

/-- Across all 4 binary input vectors and all 20 full 6-step `(3 + 3)` interleavings, both
processes decide in agreement on one of the initial inputs. -/
theorem tasProtoFin2_all_interleavings :
    ([false, true].all fun b₀ =>
      [false, true].all fun b₁ =>
        let inp : Fin 2 → Bool := fun p => if p = 0 then b₀ else b₁
        (interleavings 3 3).all (checkTASRun inp)) = true := by
  decide

/-- Both processes can win depending on who reaches `TestAndSet` first:
* in `[0, 0, 1, 1, 0, 1]`, process `0` reaches `TestAndSet` first and both decide `inp 0 = false`;
* in `[0, 1, 1, 0, 1, 0]`, process `0` writes its register first, then process `1` writes and
  reaches `TestAndSet` first, so both decide `inp 1 = true`. -/
theorem tasProtoFin2_schedule_sensitivity :
    let inp : Fin 2 → Bool := fun p => decide (p = 1)
    let c₀ := tasProtoFin2.run [0, 0, 1, 1, 0, 1] (tasProtoFin2.initConfig inp)
    let c₁ := tasProtoFin2.run [0, 1, 1, 0, 1, 0] (tasProtoFin2.initConfig inp)
    (c₀.proc 0).decided = some false ∧ (c₀.proc 1).decided = some false ∧
    (c₁.proc 0).decided = some true ∧ (c₁.proc 1).decided = some true := by
  decide

/-- Wait-free crash resilience: if process `0` crashes right after Step 1 (`[0, 1, 1, 1]`),
process `1` still decides `inp 1 = true` in 3 of its own steps. -/
theorem tasProtoFin2_crash_after_write :
    let inp : Fin 2 → Bool := fun p => decide (p = 1)
    let c := tasProtoFin2.run [0, 1, 1, 1] (tasProtoFin2.initConfig inp)
    (c.proc 0).decided = none ∧ (c.proc 1).decided = some true := by
  decide

/-- Concrete 3-process failure of `testAndSetProtocol`: with `Fin 3` and peer map `(p + 1) % 3`,
when process `2` (input `true`) wins `TestAndSet`, loser `0` (input `false`) reads register `1`
(input `false`) instead of `2`, so `0` decides `false` while `2` decides `true`! -/
theorem tasProto_fin3_disagrees :
    let π := testAndSetProtocol (P := Fin 3) id false (fun p => p + 1)
    let inp : Fin 3 → Bool := fun p => decide (p = 2)
    let c := π.run [1, 2, 2, 0, 0, 2, 0] (π.initConfig inp)
    (c.proc 0).decided = some false ∧ (c.proc 2).decided = some true := by
  decide

/-! ### 2. `CompareAndSwap`: non-commuting/non-overwriting witness & `Fin 5` consensus -/

/-- Concrete `decide`-checked witness that `casObj (none : Option Bool)` is neither commuting nor
overwriting at `s = none` for `op₁ = CAS(none, some false)` and `op₂ = CAS(none, some true)`:
all three disjuncts of `IsCommutingOrOverwriting` evaluate to `false`. -/
theorem casObj_witness_fails_all_three :
    let obj := casObj (none : Option Bool)
    let op₁ : CASOp (Option Bool) := { expected := none, desired := some false }
    let op₂ : CASOp (Option Bool) := { expected := none, desired := some true }
    let s : Option Bool := none
    (obj.step op₂ (obj.step op₁ s).1).1 ≠ (obj.step op₁ (obj.step op₂ s).1).1 ∧
    (obj.step op₂ (obj.step op₁ s).1).1 ≠ (obj.step op₂ s).1 ∧
    (obj.step op₁ (obj.step op₂ s).1).1 ≠ (obj.step op₁ s).1 := by
  decide

example : ¬ IsCommutingOrOverwriting (casObj (none : Option Bool)) :=
  not_isCommutingOrOverwriting_casObj_option

/-- Contrast: `fetchAndAddObj (0 : ℕ)` commutes on object states (`0 + 3 + 7 = 0 + 7 + 3 = 10`)
even though callers observe distinct old values (`0` vs `3` in one order, `0` vs `7` in the other),
and `swapObj (0 : ℕ)` overwrites (`swap 9 (swap 4 0) = 9 = swap 9 0`). -/
theorem rmw_commute_and_overwrite_examples :
    let faa := fetchAndAddObj (0 : ℕ)
    let swp := swapObj (0 : ℕ)
    (faa.step 7 (faa.step 3 0).1).1 = (faa.step 3 (faa.step 7 0).1).1 ∧
    (faa.step 7 (faa.step 3 0).1).2 ≠ (faa.step 7 0).2 ∧
    (swp.step 9 (swp.step 4 0).1).1 = (swp.step 9 0).1 := by
  decide

/-- 5-process `CAS` consensus over `Fin 5`: when process `3` steps first in `[3, 1, 4, 0, 2]`,
every process decides `inp 3 = 4` in a single step, and a solo step `[2]` decides `inp 2` alone. -/
theorem casConsensus_fin5_runs :
    let π := casConsensusProtocol (Fin 5) (Fin 5)
    let inp : Fin 5 → Fin 5 := fun p => p + 1
    let cFull := π.run [3, 1, 4, 0, 2] (π.initConfig inp)
    let cSolo := π.run [2] (π.initConfig inp)
    (List.finRange 5).all (fun p => (cFull.proc p).decided == some 4) = true ∧
    (cSolo.proc 2).decided = some 3 ∧
    (cSolo.proc 0).decided = none := by
  decide

/-! ### 3. Universal construction: concurrent bank account and FIFO queue -/

/-- Operations of a sequential bank account with overdraft protection. -/
inductive BankOp where
  | deposit (amount : ℕ)
  | withdraw (amount : ℕ)
  | balance
  deriving DecidableEq

/-- Responses of the sequential bank account. -/
inductive BankResp where
  | ok (newBalance : ℕ)
  | insufficientFunds (currentBalance : ℕ)
  deriving DecidableEq

/-- Sequential bank account starting at balance `100`. -/
def bankSpec : SeqSpec ℕ BankOp BankResp where
  init := 100
  step bal
    | .deposit amt => (bal + amt, .ok (bal + amt))
    | .withdraw amt =>
      if amt ≤ bal then (bal - amt, .ok (bal - amt)) else (bal, .insufficientFunds bal)
    | .balance => (bal, .ok bal)

/-- Four concurrent/staggered bank operations indexed by `Fin 4`:
* `0`: `withdraw 80` (starts at `0`)
* `1`: `withdraw 50` (starts at `0`, races with `0`)
* `2`: `deposit 60` (starts at `1`, after seeing slot `0` settled)
* `3`: `withdraw 50` (starts at `3`, after `0`, `1`, `2` have all completed!) -/
def bankOps : Fin 4 → BankOp
  | 0 => .withdraw 80
  | 1 => .withdraw 50
  | 2 => .deposit 60
  | 3 => .withdraw 50

def bankStartSlot : Fin 4 → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 3

/-- Agreed consensus slot winners: `0` wins slot `0` (balance `100 → 20`), `2` wins slot `1`
(balance `20 → 80`), `1` wins slot `2` (balance `80 → 30`, succeeding because `2`'s deposit won
slot `1` ahead of `1`!), and `3` wins slot `3` (`30 < 50`, returning `insufficientFunds 30`). -/
def bankWinner : ℕ → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | _ => 3

def bankSlots (k : ℕ) : ConsensusCell (Fin 4 × BankOp) :=
  ConsensusCell.ofWinner (bankWinner k, bankOps (bankWinner k))

theorem bank_universal_execution :
    universalInvoke bankSpec bankSlots 0 (bankOps 0) (bankStartSlot 0) =
      some { slotIdx := 0, resp := .ok 20 } ∧
    universalInvoke bankSpec bankSlots 2 (bankOps 2) (bankStartSlot 2) =
      some { slotIdx := 1, resp := .ok 80 } ∧
    universalInvoke bankSpec bankSlots 1 (bankOps 1) (bankStartSlot 1) =
      some { slotIdx := 2, resp := .ok 30 } ∧
    universalInvoke bankSpec bankSlots 3 (bankOps 3) (bankStartSlot 3) =
      some { slotIdx := 3, resp := .insufficientFunds 30 } ∧
    applyLog bankSpec (slotLog bankSlots (0, bankOps 0) 4) = 30 := by
  decide

/-- Proof that `bankSlots` satisfies `ValidSlotSchedule`, making
`universalInvoke_linearizable_of_validSlotSchedule` concrete and non-vacuous on staggered real-time
operations (`0`, `1`, `2` all precede `3`!). -/
theorem validSlotSchedule_bankSlots :
    ValidSlotSchedule bankSlots bankOps bankStartSlot := by
  have hno_active_ge4 : ∀ m, ¬ SlotActive bankSlots bankOps bankStartSlot (m + 4) := by
    intro m hact
    rcases hact with ⟨r, hr⟩ | ⟨r, _, hnot⟩
    · match r with
      | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => simp only [bankStartSlot] at hr; omega
      | ⟨_ + 4, hlt⟩ => omega
    · match r with
      | ⟨0, _⟩ => exact hnot 0 (by omega) rfl
      | ⟨1, _⟩ => exact hnot 2 (by omega) rfl
      | ⟨2, _⟩ => exact hnot 1 (by omega) rfl
      | ⟨3, _⟩ => exact hnot 3 (by omega) rfl
      | ⟨_ + 4, hlt⟩ => omega
  refine ⟨fun _ _ _ => rfl, fun k hact _ => ?_, fun k hact j hjk _ => ?_⟩
  · dsimp only [bankSlots, ConsensusCell.ofWinner]
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | m + 4 => exact absurd hact (hno_active_ge4 m)
  · dsimp only [bankSlots, ConsensusCell.ofWinner]
    match k with
    | 0 => omega
    | 1 =>
      have hj : j = 0 := by omega
      subst hj
      decide
    | 2 =>
      have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl <;> decide
    | 3 =>
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl | rfl <;> decide
    | m + 4 => exact absurd hact (hno_active_ge4 m)

example :
    ∃ res : Fin 4 → UniversalResult BankResp,
      (∀ p, universalInvoke bankSpec bankSlots p (bankOps p) (bankStartSlot p) = some (res p)) ∧
      Function.Injective (fun p => (res p).slotIdx) ∧
      (∀ p q, (res p).slotIdx < bankStartSlot q → (res p).slotIdx < (res q).slotIdx) := by
  obtain ⟨res, hres, hinj, hprec, _⟩ :=
    universalInvoke_linearizable_of_validSlotSchedule bankSpec validSlotSchedule_bankSlots
  exact ⟨res, hres, hinj, hprec⟩

/-- Concurrent FIFO queue state machine (`enqueue` / `dequeue`) replayed via `universalInvoke`,
also exercising `universalInvoke_slotIdx_bijective_of_validSlotSchedule` when all 4 operations
start at `0`. -/
inductive QueueOp where
  | enqueue (x : ℕ)
  | dequeue
  deriving DecidableEq

def queueSpec : SeqSpec (List ℕ) QueueOp (Option ℕ) where
  init := []
  step q
    | .enqueue x => (q ++ [x], none)
    | .dequeue =>
      match q with
      | [] => ([], none)
      | x :: xs => (xs, some x)

def queueOps : Fin 4 → QueueOp
  | 0 => .enqueue 10
  | 1 => .enqueue 20
  | 2 => .dequeue
  | 3 => .dequeue

def queueSlots (k : ℕ) : ConsensusCell (Fin 4 × QueueOp) :=
  let w : Fin 4 := match k with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3
  ConsensusCell.ofWinner (w, queueOps w)

/-- Winner order `[1 (enq 20), 2 (deq -> some 20), 0 (enq 10), 3 (deq -> some 10)]` leaves the
queue empty after returning `some 20` to caller `2` and `some 10` to caller `3`. -/
theorem queue_universal_execution :
    universalInvoke queueSpec queueSlots 1 (queueOps 1) 0 =
      some { slotIdx := 0, resp := none } ∧
    universalInvoke queueSpec queueSlots 2 (queueOps 2) 0 =
      some { slotIdx := 1, resp := some 20 } ∧
    universalInvoke queueSpec queueSlots 0 (queueOps 0) 0 =
      some { slotIdx := 2, resp := none } ∧
    universalInvoke queueSpec queueSlots 3 (queueOps 3) 0 =
      some { slotIdx := 3, resp := some 10 } ∧
    applyLog queueSpec (slotLog queueSlots (0, queueOps 0) 4) = [] := by
  decide

theorem validSlotSchedule_queueSlots :
    ValidSlotSchedule queueSlots queueOps (fun _ => 0) := by
  have hno_active_ge4 : ∀ m, ¬ SlotActive queueSlots queueOps (fun _ => 0) (m + 4) := by
    intro m hact
    rcases hact with ⟨_, hr⟩ | ⟨r, _, hnot⟩
    · exact Nat.not_lt_zero _ hr
    · match r with
      | ⟨0, _⟩ => exact hnot 2 (by omega) rfl
      | ⟨1, _⟩ => exact hnot 0 (by omega) rfl
      | ⟨2, _⟩ => exact hnot 1 (by omega) rfl
      | ⟨3, _⟩ => exact hnot 3 (by omega) rfl
      | ⟨_ + 4, hlt⟩ => omega
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => Nat.zero_le _, fun k hact j hjk _ => ?_⟩
  dsimp only [queueSlots, ConsensusCell.ofWinner]
  match k with
  | 0 => omega
  | 1 =>
    have hj : j = 0 := by omega
    subst hj; decide
  | 2 =>
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;> decide
  | 3 =>
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl <;> decide
  | m + 4 => exact absurd hact (hno_active_ge4 m)

example :
    ∃ (res : Fin 4 → UniversalResult (Option ℕ)) (order : Fin 4 ≃ Fin (Fintype.card (Fin 4))),
      (∀ p, universalInvoke queueSpec queueSlots p (queueOps p) 0 = some (res p)) ∧
      ∀ p, (order p).val = (res p).slotIdx := by
  obtain ⟨res, hres, _, _, _⟩ :=
    universalInvoke_linearizable_of_validSlotSchedule queueSpec validSlotSchedule_queueSlots
  obtain ⟨order, hord⟩ :=
    universalInvoke_slotIdx_bijective_of_validSlotSchedule validSlotSchedule_queueSlots hres
  exact ⟨res, order, hres, hord⟩

/-! ### 4. Instantiations of the `1 < 2 < ∞` hierarchy theorems -/

/-- Level 1: register consensus exists on `Fin 1`, and fails on `Fin 2`. -/
theorem register_hierarchy_fin1_and_fin2 :
    (∃ (I : Type) (_ : DecidableEq I) (Val : I → Type) (init : ∀ i, Val i) (S : Type)
      (π : Protocol (Fin 1) (fun i => registerObj (init i)) S Bool),
      π.SolvesWaitFreeConsensus) ∧
    ¬ (∃ (I : Type) (_ : DecidableEq I) (Val : I → Type) (init : ∀ i, Val i) (S : Type)
      (π : Protocol (Fin 2) (fun i => registerObj (init i)) S Bool),
      π.SolvesWaitFreeConsensus) := by
  rw [exists_register_consensus_iff, exists_register_consensus_iff]
  decide

/-- Level 2: `TestAndSet` + registers consensus exists on `Fin 2`, and fails on `Fin 3`. -/
theorem testAndSet_hierarchy_fin2_and_fin3 :
    (∃ (I : Type) (_ : DecidableEq I) (kind : I → TASRegKind.{0}) (S : Type)
      (π : Protocol (Fin 2) (fun i => (kind i).toObjSpec) S Bool),
      π.SolvesWaitFreeConsensus) ∧
    ¬ (∃ (I : Type) (_ : DecidableEq I) (kind : I → TASRegKind.{0}) (S : Type)
      (π : Protocol (Fin 3) (fun i => (kind i).toObjSpec) S Bool),
      π.SolvesWaitFreeConsensus) := by
  rw [exists_testAndSet_consensus_iff, exists_testAndSet_consensus_iff]
  decide

/-- Level 2 RMW impossibility also rules out `FetchAndAdd` and `Swap` protocols on `Fin 3`. -/
example (S : Type) (π : Protocol (Fin 3) (fun _ : Fin 4 => fetchAndAddObj (0 : ℕ)) S Bool) :
    ¬ π.SolvesWaitFreeConsensus :=
  not_waitFreeConsensus_rmw_of_three_le
    (fun _ => isCommutingOrOverwriting_fetchAndAddObj (0 : ℕ)) π
    (by decide : 3 ≤ Fintype.card (Fin 3))

example (S : Type) (π : Protocol (Fin 3) (fun _ : Fin 4 => swapObj (0 : ℕ)) S Bool) :
    ¬ π.SolvesWaitFreeConsensus :=
  not_waitFreeConsensus_rmw_of_three_le
    (fun _ => isCommutingOrOverwriting_swapObj (0 : ℕ)) π
    (by decide : 3 ≤ Fintype.card (Fin 3))

/-- Level `∞`: `casConsensusProtocol` solves wait-free consensus on `Fin n` for every `n : ℕ`
(including `n = 0, 1, 2, 3, 100`) and infinite value domains such as `ℕ`. -/
theorem cas_hierarchy_all_n (n : ℕ) :
    (casConsensusProtocol (Fin n) ℕ).SolvesWaitFreeConsensus :=
  solvesWaitFreeConsensus_cas

end CslibFrontierTests.Distributed.SharedMemory
