/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.Equivalents
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import Mathlib.Algebra.Field.ZMod

/-!
# Fixed-group Diffie–Hellman oracle reductions: checked instances

Clients of `CslibFrontier/Crypto/Computational/DiffieHellman/Equivalents.lean` under module
encapsulation with ordinary `import`:

* Composing the four cycle reductions `(a) ← (d) ← (c) ← (b) ← (a)` from a concrete CDH solver
  over `ZMod 5`.
* `decide` evaluations of all six reduction programs at `q = 5` and `q = 2`.
* Failure probes for dropping the `q = 2` branch in `cdhFromSqProg` and dropping primality
  (`q = 4`, failing on the unit `3` so `¬ SolvesInvDH`) in `invFromCDHProg`.
* Corrupted-oracle congruence checks via `OracleComp.QueriesSatisfy.interpret_congr` for
  `queriesSatisfy_sqFromInvProg` (corrupting an Inverse-DH oracle at `0`) and
  `queriesSatisfy_invFromDivProg` (corrupting a Divisible-DH oracle at zero divisor).
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

/-- For composite `q = 4`, `(q - 2)` exponentiation via `invFromCDHProg` fails on the unit
`3 : ZMod 4` (`(3 : ZMod 4)⁻¹ = 3`, whereas the program returns `3 ^ 2 = 1`), so it does not
satisfy `SolvesInvDH`, showing why `[Fact q.Prime]` is needed. -/
example :
    ¬ SolvesInvDH 4 (1 : ZMod 4)
      (fun u => OracleComp.evalPure (fun p : ZMod 4 × ZMod 4 => p.1 * p.2)
        (invFromCDHProg 4 (1 : ZMod 4) u)) ∧
      IsUnit (3 : ZMod 4) ∧
      OracleComp.evalPure (fun p : ZMod 4 × ZMod 4 => p.1 * p.2)
        (invFromCDHProg 4 (1 : ZMod 4) (3 • (1 : ZMod 4))) = (1 : ZMod 4) := by
  have hunit : IsUnit (3 : ZMod 4) := isUnit_iff_exists_inv.mpr ⟨3, by decide⟩
  have hval :
      OracleComp.evalPure (fun p : ZMod 4 × ZMod 4 => p.1 * p.2)
        (invFromCDHProg 4 (1 : ZMod 4) (3 • (1 : ZMod 4))) = (1 : ZMod 4) := by decide
  refine ⟨fun h => ?_, hunit, hval⟩
  have hinv3 : (3 : ZMod 4)⁻¹ * 3 = 1 := by
    rw [mul_comm]
    exact ZMod.mul_inv_of_unit 3 hunit
  have h3 := congrArg (· * (3 : ZMod 4)) (h 3 (by decide))
  simp only [smul_eq_mul, mul_one] at h3 ⊢
  rw [show OracleComp.evalPure (fun p : ZMod 4 × ZMod 4 => p.1 * p.2)
      (invFromCDHProg 4 (1 : ZMod 4) 3) = 1 from by simpa [smul_eq_mul] using hval,
    hinv3, one_mul] at h3
  exact (by decide : (3 : ZMod 4) ≠ 1) h3

@[expose] def badZeroInv (x : ZMod 5) : ZMod 5 :=
  if x = 0 then 3 else x ^ 3

theorem solvesInvDH_badZeroInv : SolvesInvDH 5 (1 : ZMod 5) badZeroInv := by
  intro α hα
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow : α ^ 3 * α = 1 :=
    (by decide : ∀ x : ZMod 5, x ≠ 0 → x ^ 3 * x = 1) α hα
  simp [badZeroInv, hα, eq_inv_of_mul_eq_one_left hpow]

/-- Every query emitted by `sqFromInvProg` is nonzero (`queriesSatisfy_sqFromInvProg`), so by
`OracleComp.QueriesSatisfy.interpret_congr`, corrupting `fun x => x ^ 3` at `0` (`badZeroInv`)
produces the same output at every `u : ZMod 5` and still yields a correct Square-DH solver. -/
example :
    (∀ u : ZMod 5,
      OracleComp.evalPure badZeroInv (sqFromInvProg (1 : ZMod 5) u) =
        OracleComp.evalPure (fun x : ZMod 5 => x ^ 3) (sqFromInvProg (1 : ZMod 5) u)) ∧
      SolvesSqDH 5 (1 : ZMod 5) (fun u => OracleComp.evalPure badZeroInv (sqFromInvProg 1 u)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨fun u => congrArg Id.run ?_,
    solvesSqDH_evalPure_sqFromInvProg 5 (1 : ZMod 5) solvesInvDH_badZeroInv⟩
  exact (queriesSatisfy_sqFromInvProg (1 : ZMod 5) u).interpret_congr fun q hq => by
    simp [badZeroInv, hq]

@[expose] def badZeroDiv (p : ZMod 5 × ZMod 5) : ZMod 5 :=
  if p.2 = 0 then 4 else p.1 * p.2 ^ 3

theorem solvesDivDH_badZeroDiv : SolvesDivDH 5 (1 : ZMod 5) badZeroDiv := by
  intro α β hβ
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow : β ^ 3 * β = 1 :=
    (by decide : ∀ x : ZMod 5, x ≠ 0 → x ^ 3 * x = 1) β hβ
  simp [badZeroDiv, hβ, eq_inv_of_mul_eq_one_left hpow]

/-- Every query emitted by `invFromDivProg` has nonzero second coordinate
(`queriesSatisfy_invFromDivProg`), so by `OracleComp.QueriesSatisfy.interpret_congr`, corrupting
`fun p => p.1 * p.2 ^ 3` at `p.2 = 0` (`badZeroDiv`) gives the same evaluation at every
`u : ZMod 5` and still yields a correct Inverse-DH solver. -/
example :
    (∀ u : ZMod 5,
      OracleComp.evalPure badZeroDiv (invFromDivProg (1 : ZMod 5) u) =
        OracleComp.evalPure (fun p : ZMod 5 × ZMod 5 => p.1 * p.2 ^ 3)
          (invFromDivProg (1 : ZMod 5) u)) ∧
      SolvesInvDH 5 (1 : ZMod 5)
        (fun u => OracleComp.evalPure badZeroDiv (invFromDivProg 1 u)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨fun u => congrArg Id.run ?_,
    solvesInvDH_evalPure_invFromDivProg 5 (1 : ZMod 5) solvesDivDH_badZeroDiv⟩
  exact (queriesSatisfy_invFromDivProg (1 : ZMod 5) u).interpret_congr fun p hp => by
    simp [badZeroDiv, hp]

end CslibFrontierTests.Crypto.DiffieHellmanEquivalents
