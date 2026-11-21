import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OriginalMachineVerifier
import Mathlib.Tactic.FinCases

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib.Complexity.CountingSimulation
open OuterRootLeaf

namespace CslibFrontierTests.OriginalMachineVerifier

private def stop : MultiTapeMachine.Action 0 Bool Unit Empty :=
  .step ⟨0, Fin.elim0, some true, none⟩ Empty.elim Empty.elim

private def double : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [stop, stop]

private theorem halted (x : List Bool) : double.HaltsWithin 1 (Cfg.init double.initial x) := by
  apply MultiTapeCTM.HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro i
  fin_cases i <;> exact .halt rfl

private theorem count (x : List Bool) (t : ℕ) (ht : 1 ≤ t) :
    double.acceptCount t (Cfg.init double.initial x) = 2 := by
  change double.branchCount (· == [true]) _ _ = 2
  rw [(halted x).branchCount_eq ht, (halted x).branchCount_eq_countP,
    MultiTapeCTM.runList_succ _ _ 0 () rfl]
  simp [MultiTapeCTM.actions, double, stop, MultiTapeMachine.Action.emptyOracleEquiv,
    Turing.Action.apply, Cfg.init]

-- The high bit can exceed the native transition count. It survives the physical scaling unchanged.
example : ScheduleChallenge.widen 5 ⟨3, 15, false⟩ = ⟨15, 15, false⟩ := rfl

-- Two identical accepting occurrences give the signed verdict for count two at every large clock.
-- Both signs use the same finite machine, branch budget and unscaled ordinary input format.
example {R : Type} [Finite R] (right : MultiTapeATM 2 Bool R) :
    ∃ (width states : ℕ) (P : Type) (_ : Finite P) (table : MultiTapePTM 0 Bool P)
      (st : P ≃ Fin states) (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q)
      (C t₀ : ℕ), ∀ (x : List Bool) (t : ℕ), t₀ ≤ t → ∀ budget,
      ChecksSeededContractions 0 1 right table st x (t * width) budget →
      ∀ claim : Bool, let ch : ScheduleChallenge := ⟨t, 1, claim⟩
        let start := atm.toPTM.toNTM.initCfg (encPair ScheduleChallenge.enc encBits (ch, x))
        let time := C * (x.length + (t / (Nat.log 2 (t + 2)).sqrt + 2)) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ claim = true) := by
  obtain ⟨width, states, P, hP, table, st, hw, h⟩ := exists_original_machine_verifier double
  let := hP
  obtain ⟨u, Q, hQ, atm, C, t₀, hs⟩ := h (0 : Fin 2) 1 (by decide) right
  refine ⟨width, states, P, hP, table, st, u, Q, hQ, atm, C, max 1 t₀, ?_⟩
  intro x t ht budget hb claim ch start time
  have h₁ := (Nat.le_max_left 1 t₀).trans ht
  have h₂ := h₁.trans (Nat.le_mul_of_pos_right t hw)
  let bit : Fin (t * width + 1) := ⟨1, Nat.lt_succ_of_le h₂⟩
  obtain ⟨hh, ha⟩ :=
    hs x ((Nat.le_max_right _ _).trans ht) ((halted x).mono h₁) budget hb bit claim
  refine ⟨hh, ha.trans ?_⟩
  rw [count x t h₁]
  have hbit : (2 : ℕ).testBit bit.val = true := by
    change (2 : ℕ).testBit 1 = true
    decide
  rw [hbit]
  exact eq_comm

end CslibFrontierTests.OriginalMachineVerifier
