/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaOffset.Clock

open Cslib.BitString Turing Turing.MultiTapeTM Turing.MultiTapeTM.GammaOffset

-- An empty tally selects the first token, including its low zero bit.
example {input : List Bool} (ip : Fin (input.length + 2)) (out tail : List Bool) :
    let word := eliasGamma 2 ++ tail
    RunsBetween machine (storage ip out word 0 [] 0)
      (storage ip (out ++ [false, true]) word 3 [] 0) 5 18 := by
  have hlen : (eliasGamma 2).length = 3 := by decide
  have hout : GammaStream.tokenOutput true 2 = [false, true] := by decide
  simpa only [List.flatMap_nil, List.length_nil, List.replicate_zero, List.append_nil,
    List.nil_append, hlen, hout, Nat.reduceAdd, Nat.reduceMul] using runsBetween ip out [] tail [] 2

-- An arbitrary prefix and suffix are preserved, including all cells after the fifth source bit.
example {input : List Bool} (ip : Fin (input.length + 2)) (out pre tail : List Bool) :
    let word := pre ++ [true, true] ++ eliasGamma 3 ++ tail
    RunsBetween machine (storage ip out word pre.length [true, true] 0)
      (storage ip ((out ++ [true, true]) ++ [true, true]) word (pre.length + 5) [true, true] 2)
      13 42 := by
  have hword : ([1, 1] : List ℕ).flatMap eliasGamma = [true, true] := by decide
  have hlen : (eliasGamma 3).length = 3 := by decide
  have hout : GammaStream.tokenOutput true 3 = [true, true] := by decide
  simpa only [hword, hlen, hout, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    List.reduceReplicate, Nat.add_assoc] using runsBetween ip out pre tail [1, 1] 3

-- Four arbitrary occupied tally cells request a field beyond a truncated payload. Even if the
-- marker is initially displaced, all skips together cost the remaining source length only once.
example {input : List Bool} (ip : Fin (input.length + 2)) (out : List Bool) :
    let word := [false, false, true, true]
    let tally := [false, true, false, true]
    ∃ (q d : ℕ) (result : List Bool), q ≤ 4 ∧
      RunsBetween machine (storageAt ip out word 0 2 tally 0)
        (storageAt ip result word q d tally 4) 18 57 := by
  simpa using exists_runsBetween_le ip out [false, false, true, true] 0 2 [false, true, false, true]

-- A cursor parked beyond an empty source does not move, even on a nonempty tally.
example {input : List Bool} (ip : Fin (input.length + 2)) (out : List Bool) :
    ∃ (d : ℕ) (result : List Bool), RunsBetween machine (storageAt ip out [] 5 0 [true] 0)
      (storageAt ip result [] 5 d [true] 1) 5 18 := by
  obtain ⟨q, d, result, hlo, hhi, h⟩ := exists_runsBetween_le ip out [] 5 0 [true]
  have hq : q = 5 := by simp at hhi; omega
  exact ⟨d, result, by simpa [hq] using h⟩
