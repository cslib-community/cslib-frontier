/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Oracle.FewQueries
import CslibFrontier.Computability.Complexity.Classes.TFNP.SearchToDecision

/-! Checked clients of Goldreich, Exercise 2.10: a solver of the search problem of `SAT` with
logarithmically many requests to any oracle language would put `SAT` in `P`, and a constant number
of requests is an instance of the general form. -/

set_option linter.privateModule false

namespace CslibFrontierTests.FewOracleQueries

open Cslib Complexity Turing.MultiTapeTM

/-- Logarithmically many requests to any oracle do not find satisfying assignments unless
`SAT ∈ P`. -/
example {O : Set (List Bool)} {c : ℕ} {f : Logic.PL.CNF ℕ → Option (List Bool)}
    (hf : ComputableInPolyTimeWithOracleQueries O (fun n => c * Nat.log 2 n + c) f encCNF
      (encOption encBits))
    (hsolve : SolvesSearch SAT.searchRel f) : SAT ∈ P encCNF :=
  SAT.searchRel_mem_FPSearch_iff.mp
    (mem_FPSearch_of_computableInPolyTimeWithOracleQueries_log SAT.searchRel_mem_FNP hf hsolve)

/-- A constant number of requests is the case `2 ^ c ≤ 2 ^ c` of the general form. -/
example {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop} (hR : R ∈ FNP enc)
    {O : Set (List Bool)} {c : ℕ} {f : α → Option (List Bool)}
    (hf : ComputableInPolyTimeWithOracleQueries O (fun _ => c) f enc (encOption encBits))
    (hsolve : SolvesSearch R f) : R ∈ FPSearch enc :=
  mem_FPSearch_of_computableInPolyTimeWithOracleQueries_of_two_pow_le hR
    (Polynomial.C (2 ^ c)) (fun _ => by simp) hf hsolve

end CslibFrontierTests.FewOracleQueries
