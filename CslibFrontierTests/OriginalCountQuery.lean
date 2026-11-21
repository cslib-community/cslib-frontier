import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OriginalCountQuery

open Turing Cslib.Complexity.CountingSimulation

-- Four source steps round to six block steps. Bit two moves up two positions.
example : paddedTime 4 = 6 ∧ originalCountBit (4, 2) = 4 := by decide

example {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (x : List Bool)
    (ht : M.toNTM.RunsInTime x 4) :
    (M.acceptCount x 6).testBit 4 = (M.acceptCount x 4).testBit 2 := by
  exact originalCountBit_eq_of_runsInTime M x 4 2 ht

-- A CTM replay at the same six physical steps preserves *the original* bit position.
example {k : ℕ} {S : Type} (M : MultiTapeCTM k Bool S) (x : List Bool)
    (hb : ∀ c : Cfg k Bool S x, (M.actions c).length ≤ 4)
    (hh : M.HaltsWithin 2 (Cfg.init M.initial x)) :
    ((MultiTapeCTM.CountingChoice.table (by decide : 0 < 2) M).acceptCount x 6).testBit 2 =
      (M.acceptCount 2 (Cfg.init M.initial x)).testBit 2 :=
  padded_terminalCount_testBit (by decide : 0 < 2) M x 2 2 hb hh
