import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootLeafClock

open Turing Turing.MultiTapeTM OuterRootLeafRequest
open Cslib.Complexity.CountingSimulation.OuterRootLeaf

private def template : RootBalanceRequest.Public := (⟨[], 1, ⟨4, 0, 0, 0, 0, 0, 0, 0⟩⟩, 2)

private def exampleInput (path : List Bool) (carry : Bool) : Input :=
  ⟨template, encNat 4, encNat 4, path, carry, [true, false, false, false, false]⟩

-- A zero-padded one selects the root. The valid all-zero movement table has one row.
example : active (data 0 (exampleInput [false, false] false)) = true := by decide

example : (publicRequest 0 false (exampleInput [false, false] false)).1.context.edge = 1 := by
  decide

-- The invalid pair and the wrong row count both select the constant-zero branch.
example : (word 0 false (exampleInput [true, true] false)).take 3 = [false, false, true] := by
  decide

example : active (data 0 (exampleInput [] false)) = false := by decide

-- A true claim about the carry component is rejected.
example : (word 0 true (exampleInput [false, false] true)).take 3 = [false, false, false] := by
  decide

example (w : ℕ) (hw : 1 < w) (n : ℕ) :
    ofBits ((true :: List.replicate n false).take (encNat w).length) = 1 := by
  have h : Cslib.BitString.lsbValue (true :: List.replicate n false) = 1 := by
    simp [Cslib.BitString.lsbValue]
  rw [ofBits_take_of_lt _ _ (h ▸ hw), h]
