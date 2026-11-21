/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaToken

open Cslib.BitString Turing Turing.MultiTapeTM Turing.MultiTapeTM.GammaToken

-- An arbitrary prefix, suffix, input head and previous output survive the token read.
-- Six is little-endian 011 and its gamma token has five cells.
example {input : List Bool} (ip : Fin (input.length + 2)) (pre tail out : List Bool) :
    let word := pre ++ eliasGamma 6 ++ tail
    (machine true).runFrom (config ip out word pre.length 0 (some (machine true).q₀)) 6 =
      config ip (out ++ [false, true, true]) word (pre.length + 5 : ℕ) 0 none := by
  have hn : Nat.log 2 6 = 2 := by decide
  have hb : lowBits 2 6 = [false, true] := by decide
  have hl : (eliasGamma 6).length = 5 := by decide
  simpa only [hl, hn, hb, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
    using runFrom_word true ip out pre tail 6

-- Skipping the shortest token still marks success and lands on the adjacent token.
example {input : List Bool} (ip : Fin (input.length + 2)) (out : List Bool) :
    (machine false).runFrom (config ip out (eliasGamma 1 ++ eliasGamma 7) 0 0
        (some (machine false).q₀)) 2 =
      config ip (out ++ [true]) (eliasGamma 1 ++ eliasGamma 7) 1 0 none := by
  simpa using runFrom_word false ip out [] (eliasGamma 7) 1

-- The all-word clock includes a leading-zero run with no delimiter and an incomplete payload.
example {input : List Bool} (ip : Fin (input.length + 2)) (n : ℕ) :
    ∃ t ≤ n + 1, ((machine true).runFrom
      (config ip [] (List.replicate n false) 0 0 (some false)) t).state = none := by
  simpa using exists_halts_le true false ip [] (List.replicate n false) 0 0
