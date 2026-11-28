/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! Ordinary clients of binary division, signed reduction and unary logarithms. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encNat encNat) (encPair encNat encNat) := by
  exact ComputableInPolyTime.binary_div.prod ComputableInPolyTime.binary_mod

example : ((13 : ℕ) / 5, (13 : ℕ) % 5) = (2, 3) := by decide
example : ((13 : ℕ) / 0, (13 : ℕ) % 0) = (0, 13) := by decide
example : encIntBin (-3) ≠ encIntBin 3 := by decide
example : ((-13 : ℤ) % (5 : ℤ)).toNat = 2 := by decide

example : ComputableInPolyTime
    (fun p : ℤ × ℕ => ((p.1 % (p.2 : ℤ)).toNat) + p.2)
    (encPair encIntBin encNat) encNat := by
  exact ComputableInPolyTime.binary_add.comp
    (ComputableInPolyTime.intBin_emodNat.prod (ComputableInPolyTime.snd _ _))

example : ComputableInPolyTime (fun n : ℕ => Nat.log 2 n + n)
    encUnary encUnary := by
  exact ComputableInPolyTime.unary_add.comp
    (ComputableInPolyTime.unary_log_two.prod ComputableInPolyTime.id')

-- Independent resource and output degrees enter the arithmetic client separately.
example {f : ℕ → ℕ} (hf : ComputableInDegree f encUnary encUnary 0 7) :
    ComputableInPolyTime (fun n => f n + n) encUnary encUnary := by
  exact ComputableInPolyTime.unary_add.comp
    (hf.computableInPolyTime.prod ComputableInPolyTime.id')

example : encNat ((13 : ℕ) / 5) ≠ [] := by decide
