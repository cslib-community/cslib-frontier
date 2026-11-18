/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.TQBF
import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Tokens

open Cslib Cslib.Logic.PL

-- Scalar payloads on a binder are retained; payloads on structural tokens must be zero.
example : PrefixParser.decode QBF.readToken [(.ex, 17), (.var, 17)] =
    some (QBF.ex 17 (.var 17)) := by decide
example : PrefixParser.decode QBF.readToken [(.and, 5), (.top, 0), (.bot, 0)] = none := by decide
example : PrefixParser.decode QBF.readToken [(.and, 0), (.top, 0)] = none := by decide
example : PrefixParser.decode QBF.readToken [(.top, 0), (.bot, 0)] = none := by decide
example : PrefixParser.decode QBF.readToken [] = none := by decide

-- Parsing a prefix leaves the following expression available to its caller.
example : PrefixParser.parse QBF.readToken [(.not, 0), (.top, 0), (.var, 9)] =
    some (QBF.not .top, [(.var, 9)]) := by decide

-- Deep unary syntax is a flat sequence, rather than recursively framed child encodings.
-- This execution check avoids a large kernel equality proof for the nested result.
set_option linter.hashCommand false in
#guard PrefixParser.decode QBF.readToken
    (List.replicate 128 (.not, 0) ++ [(.var, 7)]) == some (QBF.not^[128] (.var 7))

example : PrefixParser.decode ArithQBF.readToken [(.lin, 4), (.not, 0), (.var, 4)] =
    some (ArithQBF.op .lin 4 (.not (.var 4))) := by decide
example : PrefixParser.decode ArithQBF.readToken [(.or, 0), (.var, 2)] = none := by decide

-- The same parser also supports an empty result type, without choosing a default value.
example : PrefixParser.decode (fun (_ : Unit) => (none : Option (PrefixParser.Step Empty))) [] =
    none := rfl

namespace ArbitraryArity

-- The arity belongs to the token grammar, rather than being bounded by the parser API.
private def readToken : ℕ → Option (PrefixParser.Step ℕ)
  | 0 => some (.atom 5)
  | 1 => some (.node 3 fun xs => xs 0 + xs 1 + xs 2)
  | 2 => some (.node 0 fun _ => 7)
  | _ => none

example : PrefixParser.decode readToken [1, 0, 2, 0] = some 17 := by decide
example : PrefixParser.parse readToken [1, 0, 2, 0, 2] = some (17, [2]) := by decide
example : PrefixParser.decode readToken [1, 0, 2] = none := by decide
example : PrefixParser.decode readToken [1, 0, 2, 3] = none := by decide
example : PrefixParser.decode readToken [1, 0, 2, 0, 2] = none := by decide
example : PrefixParser.decode readToken [2] = some 7 := by decide
example : PrefixParser.parseFuel readToken 1 [1, 0, 2, 0] = none := by decide

-- A generic client uses the operand law without unfolding the parser's Fin construction.
example {α : Type} {arity : ℕ} (values : Fin arity → α) (rest : List α) :
    PrefixParser.parseOperands (fun input => match input with
      | [] => none
      | value :: tail => some (value, tail)) arity (List.ofFn values ++ rest) =
      some (values, rest) := by
  simpa using
    (PrefixParser.parseOperands_ofFn (tokens := fun a => [a]) values (by intros; rfl) rest)

end ArbitraryArity

-- Keep prefix injectivity independent of arithmetic tactics that add quotient axioms.
/-- info: 'Cslib.PrefixParser.append_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.PrefixParser.append_injective

/-- info: 'Cslib.Logic.PL.ArithQBF.tokens_append_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.Logic.PL.ArithQBF.tokens_append_inj
