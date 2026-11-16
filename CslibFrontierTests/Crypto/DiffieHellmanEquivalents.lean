/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.Equivalents
import Mathlib.Algebra.Field.ZMod

/-!
# Fixed-group Diffie–Hellman oracle reductions: checked instances

Clients of `CslibFrontier/Crypto/Computational/DiffieHellman/Equivalents.lean` under module
encapsulation with ordinary `import`:

* Composing the four cycle reductions `(a) ← (d) ← (c) ← (b) ← (a)` from a concrete CDH solver
  over `ZMod 5`.
* `decide` evaluations of all six reduction programs at `q = 5` and `q = 2`.
* Failure probes for dropping `q = 2` in `cdhFromSqProg` and dropping primality (`q = 4`) in
  `invFromCDHProg`.
* An Inverse-DH solver returning garbage (`3`) at `0` that still yields a correct Square-DH solver
  through `sqFromInvProg`, because `queriesSatisfy_sqFromInvProg` avoids querying `0`.
-/

public section

namespace CslibFrontierTests.Crypto.DiffieHellmanEquivalents

open Cslib Cslib.Crypto

@[expose] def cdh5 (p : ZMod 5 × ZMod 5) : ZMod 5 := p.1 * p.2

theorem solvesCDH_cdh5 : SolvesCDH 5 (1 : ZMod 5) cdh5 := by
  intro α β
  simp [cdh5]

@[expose] def divViaCycle (p : ZMod 5 × ZMod 5) : ZMod 5 :=
  OracleComp.evalPure cdh5 (divFromCDHProg 5 (1 : ZMod 5) p.1 p.2)

@[expose] def invViaCycle (u : ZMod 5) : ZMod 5 :=
  OracleComp.evalPure divViaCycle (invFromDivProg (1 : ZMod 5) u)

@[expose] def sqViaCycle (u : ZMod 5) : ZMod 5 :=
  OracleComp.evalPure invViaCycle (sqFromInvProg (1 : ZMod 5) u)

@[expose] def cdhViaCycle (p : ZMod 5 × ZMod 5) : ZMod 5 :=
  OracleComp.evalPure sqViaCycle (cdhFromSqProg 5 p.1 p.2)

/-- Composing the four cycle reductions `(a) ← (d) ← (c) ← (b) ← (a)` from `cdh5` over `ZMod 5`
produces a valid CDH solver. -/
example : SolvesCDH 5 (1 : ZMod 5) cdhViaCycle := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact solvesCDH_evalPure_cdhFromSqProg 5 (1 : ZMod 5) <|
    solvesSqDH_evalPure_sqFromInvProg 5 (1 : ZMod 5) <|
      solvesInvDH_evalPure_invFromDivProg 5 (1 : ZMod 5) <|
        solvesDivDH_evalPure_divFromCDHProg 5 (1 : ZMod 5) solvesCDH_cdh5

/-- Concrete evaluations of the reductions in `ZMod 5` and `ZMod 2` by `decide` (rewriting only
`(4 : ZMod 5)⁻¹ = 4` for the odd-prime `cdhFromSqProg` coefficient). -/
example :
    cdhViaCycle (2, 3) = 1 ∧
      OracleComp.evalPure cdh5 (sqFromCDHProg (3 : ZMod 5)) = 4 ∧
      OracleComp.evalPure (fun x : ZMod 5 => x ^ 3) (sqFromInvProg (1 : ZMod 5) 2) = 4 ∧
      OracleComp.evalPure (fun p : ZMod 5 × ZMod 5 => p.1 * p.2 ^ 3)
        (invFromDivProg (1 : ZMod 5) 3) = 2 ∧
      OracleComp.evalPure cdh5 (invFromCDHProg 5 (1 : ZMod 5) 3) = 2 ∧
      OracleComp.evalPure cdh5 (divFromCDHProg 5 (1 : ZMod 5) 3 2) = 4 ∧
      OracleComp.evalPure (fun x : ZMod 2 => x ^ 2) (cdhFromSqProg 2 (1 : ZMod 2) 1) = 1 ∧
      OracleComp.evalPure (fun x : ZMod 2 => x ^ 2) (cdhFromSqProg 2 (0 : ZMod 2) 1) = 0 ∧
      OracleComp.evalPure (fun p : ZMod 2 × ZMod 2 => p.1 * p.2)
        (invFromCDHProg 2 (1 : ZMod 2) 1) = 1 := by
  have h4 : (4 : ZMod 5)⁻¹ = 4 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact inv_eq_of_mul_eq_one_left (by decide)
  simp only [cdhViaCycle, cdhFromSqProg, h4]
  decide

/-- Without the `q = 2` branch, `4⁻¹ • (sq (u + v) - sq (u - v))` fails in `ZMod 2` at `α = β = 1`
because `4 = 0` in characteristic `2`, returning `0 ≠ 1 * 1`. -/
example :
    (4 : ZMod 2)⁻¹ • (((1 + 1 : ZMod 2) ^ 2) • (1 : ZMod 2) -
      ((1 - 1 : ZMod 2) ^ 2) • (1 : ZMod 2)) ≠ (1 * 1 : ZMod 2) • (1 : ZMod 2) := by
  decide

/-- For composite `q = 4`, `(q - 2)` exponentiation via `invFromCDHProg` fails to invert `2 ≠ 0`
in `ZMod 4`, showing why `[Fact q.Prime]` is needed. -/
example :
    ∃ α : ZMod 4, α ≠ 0 ∧
      OracleComp.evalPure (fun p : ZMod 4 × ZMod 4 => p.1 * p.2)
        (invFromCDHProg 4 (1 : ZMod 4) (α • (1 : ZMod 4))) * α ≠ 1 := by
  decide

@[expose] def badZeroInv (x : ZMod 5) : ZMod 5 :=
  if x = 0 then 3 else x ^ 3

theorem solvesInvDH_badZeroInv : SolvesInvDH 5 (1 : ZMod 5) badZeroInv := by
  intro α hα
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow : α ^ 3 * α = 1 :=
    (by decide : ∀ x : ZMod 5, x ≠ 0 → x ^ 3 * x = 1) α hα
  simp [badZeroInv, hα, eq_inv_of_mul_eq_one_left hpow]

/-- An Inverse-DH solver that returns `3` on `0` still gives a correct Square-DH solver through
`sqFromInvProg`, including on `0`, because `queriesSatisfy_sqFromInvProg` avoids querying `0`. -/
example :
    SolvesSqDH 5 (1 : ZMod 5) (fun u => OracleComp.evalPure badZeroInv (sqFromInvProg 1 u)) ∧
      OracleComp.evalPure badZeroInv (sqFromInvProg (1 : ZMod 5) 0) = 0 ∧
      OracleComp.evalPure badZeroInv (sqFromInvProg (1 : ZMod 5) 2) = 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨solvesSqDH_evalPure_sqFromInvProg 5 (1 : ZMod 5) solvesInvDH_badZeroInv, ?_⟩
  decide

end CslibFrontierTests.Crypto.DiffieHellmanEquivalents
