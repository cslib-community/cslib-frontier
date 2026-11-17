/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ThreeSum.ChanHe.Defs
public import CslibFrontier.Algorithms.WordRAM.NatLog
public import CslibFrontier.Algorithms.WordRAM.NatClog
public import CslibFrontier.Algorithms.WordRAM.NatSqrt
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Native parameters for Chan–He preprocessing

Original native programs and proofs. The parameter meanings are the existing finite mathematical
Chan–He definitions, with magnitude bound `2U` after the distinct-position frontend.
All loops and arithmetic are instructions; the program is fixed for each exponent `κ`.

## Main definitions

* `Parameters.program`: read the input header and compute the exact parameters.
* `Parameters.Output`: identify the unsigned output registers.

## Main results

* `Parameters.runs_input`: native execution from signed-encoded input with derived fits.
* `Parameters.two_pow_width_le`: words at the canonical width have polynomial magnitude.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters

open Cslib.WordRAM

namespace Math
open Cslib.Algorithms.ThreeSum

/-- A bound covering arithmetic, unsuccessful loop tests, and all output words. -/
def budget (n U : ℕ) : ℕ := 8 * (ChanHe.mPar n (2 * U) + 1) ^ 2 + 8 * U + 4 * n + 64

private theorem want_le (n U : ℕ) : ChanHe.wPar n (2 * U) + 1 ≤ ChanHe.mPar n (2 * U) :=
  Nat.le_mul_of_pos_right _ (by omega)

private theorem digits_le (n U : ℕ) : 5 * labelBits (2 * U) ≤ ChanHe.wPar n (2 * U) :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

private theorem factor_le (n U : ℕ) :
    2 * Nat.log 2 (ChanHe.wPar n (2 * U) + 1) + 4 ≤ ChanHe.mPar n (2 * U) :=
  Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

private theorem height_le (n : ℕ) : ChanHe.height n ≤ Nat.log 2 n + 2 :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

private theorem mPar_sq_le_budget (n U : ℕ) :
    8 * ChanHe.mPar n (2 * U) ^ 2 ≤ budget n U :=
  Nat.le_trans
    (Nat.le_trans
      (Nat.le_trans
        (Nat.mul_le_mul_left 8
          (Nat.pow_le_pow_left (Nat.le_add_right (ChanHe.mPar n (2 * U)) 1) 2))
        (Nat.le_add_right _ _))
      (Nat.le_add_right _ _))
    (Nat.le_add_right _ _)

private theorem mPar_le_budget (n U : ℕ) :
    ChanHe.mPar n (2 * U) ≤ budget n U := by
  have h1 : ChanHe.mPar n (2 * U) ≤ (ChanHe.mPar n (2 * U) + 1) ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_trans (Nat.le_add_right _ 1) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  exact Nat.le_trans
    (Nat.le_trans
      (Nat.le_trans (Nat.le_trans h1 (Nat.le_mul_of_pos_left _ (by decide : 0 < 8)))
        (Nat.le_add_right _ _))
      (Nat.le_add_right _ _))
    (Nat.le_add_right _ _)

private theorem linear_le_budget (n U : ℕ) : 8 * U + 4 * n + 64 ≤ budget n U :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left _ _) _) _

private theorem four_n_le_budget (n U : ℕ) : 4 * n + 64 ≤ budget n U :=
  Nat.add_le_add_right (Nat.le_add_left _ _) _

private theorem eight_U_le_budget (n U : ℕ) : 8 * U + 64 ≤ budget n U :=
  Nat.add_le_add_right (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) _

end Math

/-- Unsigned input length. -/
abbrev len : Fin 24 := 0
/-- Original magnitude bound U. -/
abbrev magnitude : Fin 24 := 1
/-- Label bits for magnitude bound 2U. -/
abbrev digits : Fin 24 := 2
/-- Recursion height. -/
abbrev height : Fin 24 := 3
/-- Recursion fuel. -/
abbrev fuel : Fin 24 := 4
/-- Number of desired primes. -/
abbrev want : Fin 24 := 5
/-- Upper bound on candidate primes. -/
abbrev primeBound : Fin 24 := 6
/-- Common packed convolution length, 8m². -/
abbrev packedLen : Fin 24 := 7
/-- Magnitude of the padding for the doubled frontend bound, 4U+1. -/
abbrev padding : Fin 24 := 8
/-- Constant one. -/
abbrev one : Fin 24 := 9
/-- Constant two. -/
abbrev two : Fin 24 := 10
/-- Constant three. -/
abbrev three : Fin 24 := 11
/-- Constant four. -/
abbrev four : Fin 24 := 12
/-- Constant five. -/
abbrev five : Fin 24 := 13
/-- Constant eight. -/
abbrev eight : Fin 24 := 14
/-- Input length plus two. -/
abbrev base : Fin 24 := 15
/-- Consumed logarithm argument. -/
abbrev quotient : Fin 24 := 16
/-- Floor logarithm of input length. -/
abbrev logLen : Fin 24 := 17
/-- Integer square root of input length. -/
abbrev root : Fin 24 := 18
/-- Number of desired primes plus one. -/
abbrev wantSucc : Fin 24 := 19
/-- Arithmetic scratch. -/
abbrev temp : Fin 24 := 20
/-- Successor square-root counter. -/
abbrev nextRoot : Fin 24 := 21
/-- Square of that counter. -/
abbrev square : Fin 24 := 22
/-- Square-root test bound. -/
abbrev rootBound : Fin 24 := 23

/-- Exact mathematical outputs; every output is an ordinary unsigned word. -/
structure Output (n U : ℕ) (x : Data 24) : Prop where
  len : x.regs len = n
  magnitude : x.regs magnitude = U
  digits : x.regs digits = Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  height : x.regs height = Cslib.Algorithms.ThreeSum.ChanHe.height n
  fuel : x.regs fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  want : x.regs want = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  primeBound : x.regs primeBound = Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  packedLen : x.regs packedLen = 8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U) ^ 2
  padding : x.regs padding = 4 * U + 1

/-- One header load, constants, and the polynomial base. -/
def setup : Code .standard 24 := ram[
  quotient ← #0; len ← *quotient; one ← #1; two ← #2; three ← #3;
  four ← #4; five ← #5; eight ← #8; base ← len + two ]

/-- Unroll only the compile-time fixed exponent `κ`, never the input length or word width.
Unlike `WordRAM.Power.program`, which loops over a runtime exponent register using counter and
constant-one scratch registers, `power κ` emits `κ + 1` straight-line instructions over `magnitude`
and `base` alone and requires no `Fits w (κ + 1)` budget premise at empty input (`n = 0`). -/
def power : ℕ → Code .standard 24
  | 0 => ram[ magnitude ← #1 ]
  | κ + 1 => .seq (power κ) (ram[ magnitude ← magnitude * base ])

/-- Register selection for a floor/ceiling logarithm with output `dst`. -/
def logRegisters (dst : Fin 24) : Fin 4 → Fin 24 := ![quotient, dst, one, two]

/-- Register selection for successive squares. -/
def sqrtRegisters : Fin 6 → Fin 24 := ![len, root, nextRoot, square, one, rootBound]

private theorem sqrt_injective : sqrtRegisters.Injective := by decide

/-- The instruction sequence after the power computation. -/
def calculate : Code .standard 24 :=
  .seq (ram[ quotient ← four * magnitude; padding ← quotient + one ])
    (.seq (NatLog.program.rename (logRegisters digits))
    (.seq (ram[ digits ← digits + one ])
    (.seq (NatSqrt.program.rename sqrtRegisters)
    (.seq (ram[ temp ← root + one; want ← five * digits; want ← want * temp;
      wantSucc ← want + one; quotient ← wantSucc ])
    (.seq (NatLog.program.rename (logRegisters temp))
    (.seq (ram[ temp ← two * temp; temp ← temp + four; primeBound ← wantSucc * temp ])
    (.seq (ram[ quotient ← len ])
    (.seq (NatLog.program.rename (logRegisters logLen))
    (.seq (ram[ quotient ← logLen + two ])
    (.seq (NatClog.program.rename (logRegisters height))
    (ram[ fuel ← three * height; fuel ← fuel - two; packedLen ← primeBound * primeBound;
      packedLen ← eight * packedLen ])))))))))))

/-- Fixed 24-register native code for each fixed polynomial magnitude exponent. -/
def program (κ : ℕ) : Code .standard 24 := .seq setup (.seq (power κ) calculate)

private theorem exec_power {w : ℕ} (κ : ℕ) (x : Data 24) (hb : 1 ≤ x.regs base)
    (hfit : Fits w (x.regs base ^ κ)) :
    ExecWithin w (power κ) x (x.set magnitude (x.regs base ^ κ)) (κ + 1) := by
  induction κ with
  | zero => simpa only [power, Nat.pow_zero] using ExecWithin.const hfit
  | succ κ ih =>
    have hprev : Fits w (x.regs base ^ κ) :=
      hfit.of_le (Nat.pow_le_pow_right hb (Nat.le_succ κ))
    have he := ih hprev
    have hm : ExecWithin w (ram[ magnitude ← magnitude * base ])
        (x.set magnitude (x.regs base ^ κ))
        (x.set magnitude (x.regs base ^ (κ + 1))) 1 := by
      have hp : Fits w (x.regs base ^ κ * x.regs base) := by
        simpa only [Nat.pow_succ] using hfit
      apply ExecWithin.of_eval (fuel := 0) (n := 1) ?_ (by decide)
      simp +decide [Code.eval, Op.eval_bin, Data.put,
        BinOp.eval, hp, magnitude, base, Nat.pow_succ, Data.set, Function.update_idem]
    exact (he.seq hm).mono (Nat.le_refl _)

/-- An explicit charged bound, including all header reads, copies and setup. Halt adds one. -/
def time (κ n U : ℕ) : ℕ := κ + 64 + 5 * Nat.sqrt n + 4 * Nat.log 2 (4 * U) +
  4 * Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1) +
  4 * Nat.log 2 n + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n

private theorem time_zero (n U : ℕ) : time 0 n U - 20 = 44 + 5 * Nat.sqrt n +
    4 * Nat.log 2 (4 * U) +
    4 * Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1) +
    4 * Nat.log 2 n + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n := by
  simp only [time, Nat.zero_add, Nat.add_assoc, Nat.sub_add_comm (by decide : 20 ≤ 64)]

private theorem exec_calculate_tail {w n U : ℕ} (k : Data 24)
    (k_len : k.regs len = n) (k_magnitude : k.regs magnitude = U)
    (k_digits : k.regs digits = Cslib.Algorithms.ThreeSum.labelBits (2 * U))
    (k_padding : k.regs padding = 4 * U + 1)
    (k_want : k.regs want = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U))
    (k_primeBound : k.regs primeBound = Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U))
    (k_logLen : k.regs logLen = Nat.log 2 n)
    (k_two : k.regs two = 2) (k_three : k.regs three = 3)
    (k_eight : k.regs eight = 8)
    (hfit : Fits w (Math.budget n U)) :
    ∃ p, ExecWithin w
      (.seq (ram[ quotient ← logLen + two ])
      (.seq (NatClog.program.rename (logRegisters height))
      (ram[ fuel ← three * height; fuel ← fuel - two; packedLen ← primeBound * primeBound;
        packedLen ← eight * packedLen ])))
      k p (10 + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n) ∧
      Output n U p ∧ p.mem = k.mem := by
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let h := Cslib.Algorithms.ThreeSum.ChanHe.height n
  let wp := Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  change k.regs digits = Λ at k_digits
  change k.regs want = wp at k_want
  change k.regs primeBound = m at k_primeBound
  have eh : Cslib.Algorithms.ThreeSum.ChanHe.fuel n = 3 * h - 2 := rfl
  have hh : h ≤ Nat.log 2 n + 2 := Math.height_le n
  have hl := Nat.log_le_self 2 n
  have hlogn4 : Nat.log 2 n ≤ 4 * n := Nat.le_trans hl (Nat.le_mul_of_pos_left n (by decide))
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (Nat.le_trans hv (Math.four_n_le_budget n U))
  have f2 : Fits w 2 := fitn 2 (Nat.le_trans (by decide : 2 ≤ 64) (Nat.le_add_left 64 _))
  have flog2 : Fits w (Nat.log 2 n + 2) := fitn _ (Nat.add_le_add hlogn4 (by decide))
  have flog3 : Fits w (Nat.log 2 n + 2 + 1) :=
    fitn _ ((Nat.add_assoc _ 2 1).symm ▸ Nat.add_le_add hlogn4 (by decide : 3 ≤ 64))
  have fh : Fits w (h + 1) := flog3.of_le (Nat.add_le_add_right hh 1)
  have f3h : Fits w (3 * h) := fitn _ (Nat.le_trans (Nat.mul_le_mul_left 3 hh)
    (Nat.mul_add 3 (Nat.log 2 n) 2 ▸ Nat.add_le_add
      (Nat.le_trans (Nat.mul_le_mul_left 3 hl) (Nat.mul_le_mul_right n (by decide : 3 ≤ 4)))
      (by decide : 6 ≤ 64)))
  have ffuel : Fits w (Cslib.Algorithms.ThreeSum.ChanHe.fuel n) := f3h.of_le (Nat.sub_le _ _)
  have fN : Fits w (8 * m ^ 2) := hfit.of_le (Math.mPar_sq_le_budget n U)
  have fNm : Fits w (8 * (m * m)) := by simpa only [Nat.pow_two] using fN
  have fm2 : Fits w (m * m) := fNm.of_le (Nat.le_mul_of_pos_left _ (by decide : 0 < 8))
  wram_exec [k_logLen, k_two, flog2]
  wram_call (NatClog.exec _ f2
    (by simp only [wram_simps, NatClog.arg, logRegisters, flog3])
    (by simp only [wram_simps, NatClog.arg, logRegisters]; exact fh)) canonical
    (by decide : (logRegisters height).Injective) with o ⟨oh, om, oo, ot⟩
  wram_exec [logRegisters, NatClog.result, NatClog.one, NatClog.two, oh, oo, ot,
    k_three, k_primeBound, k_eight, ← eh, f3h, ffuel, fm2, fNm,
    show Nat.clog 2 (Nat.log 2 n + 2) = h from rfl]
  refine ⟨?_, ?_⟩
  · refine ⟨by simp only [wram_simps, k_len], by simp only [wram_simps, k_magnitude],
      by simp only [wram_simps, k_digits, Λ],
      by simp only [wram_simps, oh, Cslib.Algorithms.ThreeSum.ChanHe.height],
      by simp only [wram_simps],
      by simp only [wram_simps, k_want, wp], by simp only [wram_simps, k_primeBound, m],
      by simp only [wram_simps, Nat.pow_two, m],
      by simp only [wram_simps, k_padding]⟩
  · simp only [wram_simps, om]

private theorem exec_calculate_suffix {w n U : ℕ} (f : Data 24)
    (f_len : f.regs len = n) (f_magnitude : f.regs magnitude = U)
    (f_digits : f.regs digits = Cslib.Algorithms.ThreeSum.labelBits (2 * U))
    (f_padding : f.regs padding = 4 * U + 1)
    (f_want : f.regs want = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U))
    (f_wantSucc : f.regs wantSucc = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1)
    (f_temp : f.regs temp = Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1))
    (f_two : f.regs two = 2) (f_three : f.regs three = 3)
    (f_four : f.regs four = 4) (f_eight : f.regs eight = 8)
    (hfit : Fits w (Math.budget n U)) :
    ∃ p, ExecWithin w
      (.seq (ram[ temp ← two * temp; temp ← temp + four; primeBound ← wantSucc * temp ])
      (.seq (ram[ quotient ← len ])
      (.seq (NatLog.program.rename (logRegisters logLen))
      (.seq (ram[ quotient ← logLen + two ])
      (.seq (NatClog.program.rename (logRegisters height))
      (ram[ fuel ← three * height; fuel ← fuel - two; packedLen ← primeBound * primeBound;
        packedLen ← eight * packedLen ]))))))
      f p (19 + 4 * Nat.log 2 n + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n) ∧
      Output n U p ∧ p.mem = f.mem := by
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let h := Cslib.Algorithms.ThreeSum.ChanHe.height n
  let wp := Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  change f.regs digits = Λ at f_digits
  change f.regs want = wp at f_want
  change f.regs wantSucc = wp + 1 at f_wantSucc
  change f.regs temp = Nat.log 2 (wp + 1) at f_temp
  have em : m = (wp + 1) * (2 * Nat.log 2 (wp + 1) + 4) := rfl
  have hf : 2 * Nat.log 2 (wp + 1) + 4 ≤ m := Math.factor_le n U
  have hl := Nat.log_le_self 2 n
  have hml : Fits w m := hfit.of_le (Math.mPar_le_budget n U)
  have fitm (v : ℕ) (hv : v ≤ m) : Fits w v := hml.of_le hv
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (Nat.le_trans hv (Math.four_n_le_budget n U))
  have f2 : Fits w 2 := fitn 2 (Nat.le_trans (by decide : 2 ≤ 64) (Nat.le_add_left 64 _))
  have f2log : Fits w (2 * Nat.log 2 (wp + 1)) := fitm _ (Nat.le_trans (Nat.le_add_right _ 4) hf)
  have ff : Fits w (2 * Nat.log 2 (wp + 1) + 4) := fitm _ hf
  have fn : Fits w n :=
    fitn n (Nat.le_trans (Nat.le_mul_of_pos_left n (by decide)) (Nat.le_add_right _ 64))
  have flogn : Fits w (Nat.log 2 n + 1) :=
    fitn _ (Nat.add_le_add (Nat.le_trans hl (Nat.le_mul_of_pos_left n (by decide))) (by decide))
  wram_exec [f_two, f_temp, f_four, f_wantSucc, ← em, f2log, ff, hml, f_len]
  wram_call (NatLog.exec _ f2
    (by simp only [wram_simps, NatLog.arg, logRegisters, fn])
    (by simp only [wram_simps, NatLog.arg, logRegisters, flogn])) canonical
    (by decide : (logRegisters logLen).Injective) with k ⟨kl, km, _, kt⟩
  wram_call (exec_calculate_tail _
    (by simp only [wram_simps, f_len]) (by simp only [wram_simps, f_magnitude])
    (by simp only [wram_simps, f_digits, Λ]) (by simp only [wram_simps, f_padding])
    (by simp only [wram_simps, f_want, wp]) (by simp only [wram_simps, m])
    (by simp only [wram_simps, kl])
    (by simp only [wram_simps, kt])
    (by simp only [wram_simps, f_three]) (by simp only [wram_simps, f_eight]) hfit) with p ⟨hp, hm⟩
  refine ⟨?_, hp, ?_⟩
  · simp only [wram_simps]
    omega
  · simp only [wram_simps, hm, km]

private theorem exec_calculate {w n U : ℕ} (x : Data 24)
    (hlen : x.regs len = n) (hU : x.regs magnitude = U)
    (h1 : x.regs one = 1) (h3 : x.regs three = 3)
    (h4 : x.regs four = 4) (h5 : x.regs five = 5) (h8 : x.regs eight = 8)
    (hfit : Fits w (Math.budget n U)) :
    ∃ y, ExecWithin w calculate x y (time 0 n U - 20) ∧ Output n U y ∧ y.mem = x.mem := by
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let h := Cslib.Algorithms.ThreeSum.ChanHe.height n
  let wp := Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  have eΛ : Λ = Nat.log 2 (4 * U) + 1 := by
    dsimp only [Λ, Cslib.Algorithms.ThreeSum.labelBits]
    rw [← Nat.mul_assoc]
  have ew : wp = 5 * Λ * (Nat.sqrt n + 1) := rfl
  have hd : 5 * Λ ≤ wp := Math.digits_le n U
  have hw : wp + 1 ≤ m := Math.want_le n U
  have hf : 2 * Nat.log 2 (wp + 1) + 4 ≤ m := Math.factor_le n U
  have hroot := Nat.sqrt_le_self n
  have hml : Fits w m := hfit.of_le (Math.mPar_le_budget n U)
  have fitm (v : ℕ) (hv : v ≤ m) : Fits w v := hml.of_le hv
  have fitu (v : ℕ) (hv : v ≤ 8 * U + 64) : Fits w v :=
    hfit.of_le (Nat.le_trans hv (Math.eight_U_le_budget n U))
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (Nat.le_trans hv (Math.four_n_le_budget n U))
  have f2 : Fits w 2 := fitu 2 (Nat.le_trans (by decide : 2 ≤ 64) (Nat.le_add_left 64 _))
  have h4U8 : 4 * U ≤ 8 * U := Nat.mul_le_mul_right U (by decide)
  have f4U : Fits w (4 * U) := fitu _ (Nat.le_trans h4U8 (Nat.le_add_right _ 64))
  have fpad : Fits w (4 * U + 1) := fitu _ (Nat.add_le_add h4U8 (by decide))
  have fwp : Fits w wp := fitm _ (Nat.le_trans (Nat.le_add_right wp 1) hw)
  have f5Λ : Fits w (5 * Λ) := fwp.of_le hd
  have fΛ : Fits w Λ := f5Λ.of_le (Nat.le_mul_of_pos_left Λ (by decide))
  have flogU : Fits w (Nat.log 2 (4 * U) + 1) := eΛ ▸ fΛ
  have fsqrt : Fits w (4 * n + 4) := fitn _ (Nat.add_le_add_left (by decide) _)
  have fr : Fits w (Nat.sqrt n + 1) :=
    fitn _ (Nat.add_le_add (Nat.le_trans hroot (Nat.le_mul_of_pos_left n (by decide))) (by decide))
  have fwps : Fits w (wp + 1) := fitm _ hw
  have flogwp : Fits w (Nat.log 2 (wp + 1) + 1) :=
    fitm _ (Nat.le_trans (Nat.add_le_add (Nat.le_mul_of_pos_left _ (by decide)) (by decide)) hf)
  unfold calculate
  wram_exec [h4, hU, h1, f4U, fpad]
  wram_call (NatLog.exec _ f2
    (by simp only [wram_simps, NatLog.arg, logRegisters, f4U])
    (by simp only [wram_simps, NatLog.arg, logRegisters, flogU])) canonical
    (by decide : (logRegisters digits).Injective) with b ⟨bd, bm, bo, bt⟩
  wram_exec [logRegisters, NatLog.result, NatLog.one, bd, bo, ← eΛ, fΛ]
  wram_call (NatSqrt.exec _
    (by simp only [wram_simps, sqrtRegisters, NatSqrt.arg, hlen, fsqrt])) canonical
    sqrt_injective with d ⟨dr, dl, dm, done⟩
  wram_exec [sqrtRegisters, NatSqrt.root, NatSqrt.one, dr, done, hlen,
    logRegisters, h5, ← ew, fr, f5Λ, fwp, fwps, ← eΛ]
  wram_call (NatLog.exec _ f2
    (by simp only [wram_simps, NatLog.arg, logRegisters, fwps])
    (by simp only [wram_simps, NatLog.arg, logRegisters, flogwp])) canonical
    (by decide : (logRegisters temp).Injective) with f ⟨ft, fm, _, ftt⟩
  wram_call (exec_calculate_suffix _
    (by simp only [wram_simps, sqrtRegisters, NatSqrt.arg, dl, hlen])
    (by simp only [wram_simps, hU]) (by simp only [wram_simps, Λ])
    (by simp only [wram_simps]) (by simp only [wram_simps, wp]) (by simp only [wram_simps, wp])
    (by simp only [wram_simps, ft, wp])
    (by simp only [wram_simps, ftt])
    (by simp only [wram_simps, h3]) (by simp only [wram_simps, h4])
    (by simp only [wram_simps, h8]) hfit) with p ⟨hp, hm⟩
  refine ⟨?_, hp, ?_⟩
  · simp only [wram_simps, time_zero, sqrtRegisters, NatSqrt.arg, hlen, wp]
    omega
  · simp only [wram_simps, hm, fm, dm, bm]

private theorem time_exec_le (κ n U : ℕ) :
    (time 0 n U - 20) + (κ + 1) + 9 ≤ time κ n U := by
  have h1 : time κ n U = κ + time 0 n U := by
    simp only [time, Nat.zero_add, Nat.add_assoc]
  have h2 : 20 ≤ time 0 n U := by
    simp only [time, Nat.zero_add, Nat.add_assoc]
    exact Nat.le_trans (by decide : 20 ≤ 64) (Nat.le_add_right _ _)
  omega

/-- Read the native unsigned header and compute all parameters, preserving every memory cell.
This local theorem is discharged from a logarithmic width in `runs_input`. -/
theorem exec {w : ℕ} (κ : ℕ) (x : Data 24)
    (hfit : Fits w (Math.budget (x.mem 0) ((x.mem 0 + 2) ^ κ))) :
    ∃ y, ExecWithin w (program κ) x y (time κ (x.mem 0) ((x.mem 0 + 2) ^ κ)) ∧
      Output (x.mem 0) ((x.mem 0 + 2) ^ κ) y ∧ y.mem = x.mem := by
  let n := x.mem 0
  let U := (n + 2) ^ κ
  have fit (v : ℕ) (hv : v ≤ 8 * U + 4 * n + 64) : Fits w v :=
    hfit.of_le (Nat.le_trans hv (Math.linear_le_budget n U))
  have fit64 (v : ℕ) (hv : v ≤ 64) : Fits w v := fit v (Nat.le_trans hv (Nat.le_add_left 64 _))
  have f0 : Fits w 0 := fit64 0 (by decide)
  have f1 : Fits w 1 := fit64 1 (by decide)
  have f2 : Fits w 2 := fit64 2 (by decide)
  have f3 : Fits w 3 := fit64 3 (by decide)
  have f4 : Fits w 4 := fit64 4 (by decide)
  have f5 : Fits w 5 := fit64 5 (by decide)
  have f8 : Fits w 8 := fit64 8 (by decide)
  have fb : Fits w (n + 2) :=
    hfit.of_le (Nat.le_trans
      (Nat.add_le_add (Nat.le_mul_of_pos_left n (by decide)) (by decide))
      (Math.four_n_le_budget n U))
  have fn : Fits w n := fb.of_le (Nat.le_add_right n 2)
  have fU : Fits w U :=
    hfit.of_le (Nat.le_trans
      (Nat.le_trans (Nat.le_mul_of_pos_left U (by decide)) (Nat.le_add_right _ 64))
      (Math.eight_U_le_budget n U))
  unfold program setup
  wram_exec [f0, fn, f1, f2, f3, f4, f5, f8, fb]
  refine WP.of_execWithin
    (exec_power κ _ (by simp only [wram_simps]; exact Nat.succ_pos _)
      (by simp only [wram_simps, fU, U, n])) ?_
  wram_call (exec_calculate _
    (by simp only [wram_simps]) (by simp only [wram_simps]) (by simp only [wram_simps])
    (by simp only [wram_simps]) (by simp only [wram_simps]) (by simp only [wram_simps])
    (by simp only [wram_simps]) hfit) with y ⟨hout, hm⟩
  refine ⟨?_, hout, ?_⟩
  · exact time_exec_le κ n U
  · simp only [wram_simps, hm]

namespace Math

open Cslib.Algorithms.ThreeSum

/-- A polynomial scale for bounding every parameter intermediate. -/
def scale (n U : ℕ) : ℕ := 16 * (n + 2) * (U + 1)

private theorem scale_bounds (n U : ℕ) :
    16 ≤ scale n U ∧ n + 2 ≤ scale n U ∧ 4 * U + 2 ≤ scale n U := by
  have h16 : 16 ≤ scale n U :=
    Nat.le_trans (Nat.le_mul_of_pos_right 16 (Nat.succ_pos _))
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hn : n + 2 ≤ scale n U :=
    Nat.le_trans (Nat.le_mul_of_pos_left (n + 2) (by decide : 0 < 16))
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hU : 4 * U + 2 ≤ scale n U :=
    Nat.le_trans
      (Nat.mul_succ 4 U ▸ Nat.add_le_add_left (by decide : 2 ≤ 4) (4 * U))
      (Nat.mul_le_mul_right (U + 1)
        (Nat.le_trans (by decide : 4 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos _))))
  exact ⟨h16, hn, hU⟩

private theorem scale_pow_mono {b : ℕ} (hb : 1 ≤ b) {i j : ℕ} (hij : i ≤ j) :
    b ^ i ≤ b ^ j := Nat.pow_le_pow_right hb hij

/-- A coarse polynomial bound; it also covers final unsuccessful root/log iterations. -/
theorem budget_le_scale (n U : ℕ) : budget n U ≤ scale n U ^ 20 := by
  obtain ⟨hb, hn, hU⟩ := scale_bounds n U
  generalize scale n U = b at hb hn hU ⊢
  have hsmall : 8 * U + 4 * n + 64 ≤ 16 * b := by omega
  have hb1 : 1 ≤ b := Nat.le_trans (by decide : 1 ≤ 16) hb
  have hΛ : labelBits (2 * U) ≤ b := by
    have hl : Nat.log 2 (4 * U) ≤ 4 * U := Nat.log_le_self 2 (4 * U)
    dsimp only [labelBits]
    rw [← Nat.mul_assoc]
    exact Nat.le_trans (Nat.add_le_add hl (by decide : 1 ≤ 2)) hU
  have hr : Nat.sqrt n + 1 ≤ b :=
    Nat.le_trans (Nat.add_le_add (Nat.sqrt_le_self n) (by decide : 1 ≤ 2)) hn
  have hw : ChanHe.wPar n (2 * U) ≤ b ^ 3 := by
    have h1 : ChanHe.wPar n (2 * U) ≤ b * b * b :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_trans (by decide : 5 ≤ 16) hb) hΛ) hr
    rwa [← Nat.pow_two, ← Nat.pow_succ] at h1
  have hws : ChanHe.wPar n (2 * U) + 1 ≤ b ^ 4 := by
    have h1 : ChanHe.wPar n (2 * U) + 1 ≤ 2 * b ^ 3 := by
      rw [Nat.two_mul (b ^ 3)]
      exact Nat.add_le_add hw (Nat.one_le_pow _ _ hb1)
    have h2 : 2 * b ^ 3 ≤ b * b ^ 3 :=
      Nat.mul_le_mul_right _ (Nat.le_trans (by decide : 2 ≤ 16) hb)
    rw [← Nat.pow_succ'] at h2
    exact Nat.le_trans h1 h2
  have hfac : 2 * Nat.log 2 (ChanHe.wPar n (2 * U) + 1) + 4 ≤ b ^ 5 := by
    have hl : Nat.log 2 (ChanHe.wPar n (2 * U) + 1) ≤ b ^ 4 :=
      Nat.le_trans (Nat.log_le_self 2 _) hws
    have h1 : 2 * Nat.log 2 (ChanHe.wPar n (2 * U) + 1) + 4 ≤ 6 * b ^ 4 := by
      have h2 := Nat.add_le_add (Nat.mul_le_mul_left 2 hl)
        (Nat.mul_le_mul_left 4 (Nat.one_le_pow 4 b hb1))
      rwa [← Nat.add_mul] at h2
    have h3 : 6 * b ^ 4 ≤ b * b ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.le_trans (by decide : 6 ≤ 16) hb)
    rw [← Nat.pow_succ'] at h3
    exact Nat.le_trans h1 h3
  have hm : ChanHe.mPar n (2 * U) ≤ b ^ 9 := by
    have h1 := Nat.mul_le_mul hws hfac
    rwa [← Nat.pow_add] at h1
  have hms : ChanHe.mPar n (2 * U) + 1 ≤ 2 * b ^ 9 := by
    rw [Nat.two_mul (b ^ 9)]
    exact Nat.add_le_add hm (Nat.one_le_pow _ _ hb1)
  have hsq : (ChanHe.mPar n (2 * U) + 1) ^ 2 ≤ 4 * b ^ 18 := by
    have h1 := Nat.pow_le_pow_left hms 2
    rwa [Nat.mul_pow, ← Nat.pow_mul] at h1
  have hp18 : b ≤ b ^ 18 := by
    simpa only [Nat.pow_one] using scale_pow_mono hb1 (show 1 ≤ 18 by decide)
  have hbudget : budget n U ≤ 48 * b ^ 18 := by
    have h8 : 8 * (ChanHe.mPar n (2 * U) + 1) ^ 2 ≤ 32 * b ^ 18 := by
      have h1 := Nat.mul_le_mul_left 8 hsq
      rwa [← Nat.mul_assoc] at h1
    have h16 : 8 * U + 4 * n + 64 ≤ 16 * b ^ 18 :=
      Nat.le_trans hsmall (Nat.mul_le_mul_left 16 hp18)
    have hsum := Nat.add_le_add h8 h16
    rw [← Nat.add_mul] at hsum
    dsimp only [budget]
    rwa [Nat.add_assoc, Nat.add_assoc, ← Nat.add_assoc (8 * U)]
  have h48 : 48 ≤ b ^ 2 :=
    Nat.le_trans (by decide : 48 ≤ 16 ^ 2) (Nat.pow_le_pow_left hb 2)
  have hfin := Nat.le_trans hbudget (Nat.mul_le_mul_right _ h48)
  rwa [← Nat.pow_add] at hfin

/-- A single polynomial bound, with exponent affine in the fixed magnitude exponent. -/
theorem budget_polynomial (κ n : ℕ) : budget n ((n + 2) ^ κ) ≤ (n + 2) ^ (20 * κ + 120) := by
  let a := n + 2
  have ha : 2 ≤ a := Nat.le_add_left 2 n
  have hpow : 1 ≤ a ^ κ := Nat.one_le_pow _ _ (Nat.le_trans (by decide : 1 ≤ 2) ha)
  have h32 : 32 ≤ a ^ 5 :=
    Nat.le_trans (by decide : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_left ha 5)
  have hs : scale n (a ^ κ) ≤ a ^ (κ + 6) := by
    have h1 : scale n (a ^ κ) ≤ 16 * a * (2 * a ^ κ) :=
      Nat.mul_le_mul_left (16 * a) (by rw [Nat.two_mul]; exact Nat.add_le_add_left hpow _)
    rw [← Nat.mul_assoc, Nat.mul_right_comm 16 a 2] at h1
    have h2 : 32 * a * a ^ κ ≤ a ^ 5 * a * a ^ κ :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h32)
    rw [← Nat.pow_succ, ← Nat.pow_add, Nat.add_comm] at h2
    exact Nat.le_trans h1 h2
  have hfin := Nat.le_trans (budget_le_scale n (a ^ κ)) (Nat.pow_le_pow_left hs 20)
  rwa [← Nat.pow_mul, Nat.mul_comm, Nat.mul_add] at hfin

end Math
/-- Positive logarithmic word-width threshold for the complete parameter computation. -/
def width (κ n : ℕ) : ℕ := (20 * κ + 121) * Nat.clog 2 (n + 2)

/-- The width requirement is satisfiable even at empty input and exponent zero. -/
theorem width_pos (κ n : ℕ) : 0 < width κ n :=
  Nat.mul_pos (Nat.succ_pos _)
    (Nat.clog_pos (b := 2) (by decide) (Nat.succ_lt_succ (Nat.succ_pos n)))

private theorem budget_le_two_pow (κ n : ℕ) :
    Math.budget n ((n + 2) ^ κ) ≤ 2 ^ ((20 * κ + 120) * Nat.clog 2 (n + 2)) := by
  have h := Nat.le_trans (Math.budget_polynomial κ n)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) (n + 2)) _)
  rwa [← Nat.pow_mul, Nat.mul_comm] at h

/-- Every local fit premise follows from the positive logarithmic width. -/
theorem budget_fits {κ n w : ℕ} (hw : width κ n ≤ w) :
    Fits w (Math.budget n ((n + 2) ^ κ)) := by
  have hl := Nat.clog_pos (b := 2) (by decide) (Nat.succ_lt_succ (Nat.succ_pos n))
  apply Fits.mono (w := width κ n) _ hw
  apply Nat.lt_of_le_of_lt (budget_le_two_pow κ n)
  apply Nat.pow_lt_pow_right (by decide)
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hl

/-- Signed-encoded inputs and the unsigned length header fit at the same width. -/
theorem inputFits {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    InputFits w (input.map Signed.encode) := by
  have hf := budget_fits hw
  refine ⟨?_, ?_⟩
  · rw [List.length_map]
    exact hf.of_le (Nat.le_trans
      (Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide)) (Nat.le_add_right _ 64))
      (Math.four_n_le_budget _ _))
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have habs : z.natAbs ≤ (input.length + 2) ^ κ :=
      Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hvalues z hz)
    have hbit : (if z < 0 then 1 else 0) ≤ 64 := by split <;> decide
    have henc : Signed.encode z ≤ 8 * (input.length + 2) ^ κ + 64 :=
      Nat.add_le_add
        (Nat.le_trans (Nat.mul_le_mul_left 2 habs) (Nat.mul_le_mul_right _ (by decide : 2 ≤ 8)))
        hbit
    exact hf.of_le (Nat.le_trans henc (Math.eight_U_le_budget _ _))

private theorem time_bound_arith {κ a b c d S EL L : ℕ}
    (ha : a ≤ EL) (hb : b ≤ EL) (hc : c ≤ EL) (hd : d ≤ c + 2)
    (h1 : κ + 74 ≤ (κ + 74) * L) (h2 : 17 * EL + (κ + 74) * L ≤ (400 * κ + 3000) * L) :
    κ + 64 + S + 4 * a + 4 * b + 4 * c + 5 * d ≤ S + (400 * κ + 3000) * L := by
  omega

/-- Explicit `Oκ(√n + log(n+2))` instruction bound, valid also at `n = 0,1,2`. -/
theorem time_bound (κ n : ℕ) :
    time κ n ((n + 2) ^ κ) ≤
      5 * Nat.sqrt n + (400 * κ + 3000) * Nat.clog 2 (n + 2) := by
  let U := (n + 2) ^ κ
  let L := Nat.clog 2 (n + 2)
  let E := 20 * κ + 120
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (Nat.succ_lt_succ (Nat.succ_pos n))
  have hB : Nat.log 2 (Math.budget n U) ≤ E * L := by
    have h := Nat.log_mono_right (b := 2) (budget_le_two_pow κ n)
    rwa [Nat.log_pow (by decide)] at h
  have hlogU : Nat.log 2 (4 * U) ≤ E * L :=
    Nat.le_trans (Nat.log_mono_right (Nat.le_trans
      (Nat.le_trans (Nat.mul_le_mul_right U (by decide : 4 ≤ 8)) (Nat.le_add_right _ 64))
      (Math.eight_U_le_budget n U))) hB
  have hlogw : Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1) ≤ E * L :=
    Nat.le_trans (Nat.log_mono_right (Nat.le_trans (Math.want_le n U) (Math.mPar_le_budget n U))) hB
  have hlogn : Nat.log 2 n ≤ E * L :=
    Nat.le_trans (Nat.log_mono_right (Nat.le_trans
      (Nat.le_trans (Nat.le_mul_of_pos_left n (by decide : 0 < 4)) (Nat.le_add_right _ 64))
      (Math.four_n_le_budget n U))) hB
  have hh := Math.height_le n
  have hκ : κ + 74 ≤ (κ + 74) * L := Nat.le_mul_of_pos_right _ hL
  have hcoeff : 17 * (E * L) + (κ + 74) * L ≤ (400 * κ + 3000) * L := by
    rw [← Nat.mul_assoc, ← Nat.add_mul]
    apply Nat.mul_le_mul_right L
    dsimp only [E]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc (340 * κ), Nat.add_left_comm 2040 κ,
      ← Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right κ (by decide)) (by decide)
  exact time_bound_arith hlogU hlogw hlogn hh hκ hcoeff

/-- Native run from actual signed input initialization. No parameters or arithmetic routines
are supplied as advice. The returned state identifies all outputs and keeps *all* input memory.
The flat program has 24 registers and depends only on `κ`; halting adds one instruction. -/
theorem runs_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ y t, t ≤ 5 * Nat.sqrt input.length +
        (400 * κ + 3000) * Nat.clog 2 (input.length + 2) ∧
      Runs w ((program κ).program packedLen) (State.init (input.map Signed.encode))
        ⟨(program κ).size, y⟩ t ∧
      Output input.length ((input.length + 2) ^ κ) y ∧
      y.mem = (Data.init (input.map Signed.encode) : Data 24).mem ∧ y.Bounded w := by
  have hi := inputFits input hw hvalues
  obtain ⟨y, hy, ho, hm⟩ := exec κ (Data.init (input.map Signed.encode))
    (by simpa only [Data.init_mem_zero, List.length_map] using budget_fits hw)
  simp only [Data.init_mem_zero, List.length_map] at hy ho
  obtain ⟨t, ht, he⟩ := hy
  have hr := he.runs (pc := 0) (p := (program κ).program packedLen)
    (Program.Contains.self _).append_left
  simp only [Nat.zero_add] at hr
  refine ⟨y, t, ht.trans (time_bound κ input.length), hr, ho, hm, ?_⟩
  exact hr.bounded_init hi

/-- The number of native instructions in the finite structured code is affine in `κ`. -/
theorem size_program (κ : ℕ) : (program κ).size = κ + 71 := by
  have hp : (power κ).size = κ + 1 := by
    induction κ with
    | zero => rfl
    | succ κ ih => simp [power, ih]
  simp only [program, setup, calculate, NatLog.program, NatLog.body, NatSqrt.program,
    NatSqrt.body, NatClog.program, NatClog.body, Code.size.eq_2, Code.size, Nat.reduceAdd, hp,
    Code.size_rename]
  omega

/-- The code is the same at every word width. -/
theorem not_readsWidth (κ : ℕ) : ¬(program κ).ReadsWidth := by
  have hs : ¬setup.ReadsWidth := by decide
  have hc : ¬calculate.ReadsWidth := by decide
  have hp : ¬(power κ).ReadsWidth := by
    induction κ with
    | zero => decide
    | succ κ ih =>
      change ¬((power κ).ReadsWidth ∨
        (Code.op (Op.bin BinOp.mul magnitude magnitude base) : Code .standard 24).ReadsWidth)
      exact not_or.mpr ⟨ih, by decide⟩
  exact fun h => h.elim hs fun h => h.elim hp hc

/-- A word at the canonical width has polynomial magnitude. -/
theorem two_pow_width_le (κ n : ℕ) : 2 ^ width κ n ≤ (n + 2) ^ (40 * κ + 242) := by
  have hpow := Nat.pow_clog_le_mul (by decide : 1 < 2) (Nat.succ_ne_zero (n + 1))
  have hsq : 2 * (n + 2) ≤ (n + 2) ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_right (n + 2) (Nat.le_add_left 2 n)
  have h := Nat.pow_le_pow_left (Nat.le_trans hpow hsq) (20 * κ + 121)
  rw [← Nat.pow_mul, Nat.mul_comm (Nat.clog 2 (n + 2)),
    ← Nat.pow_mul, Nat.mul_add, ← Nat.mul_assoc] at h
  exact h

/-- Canonical-width executions use only polynomially bounded integers, including memory
addresses, loop counters, and final unsuccessful tests. -/
theorem intermediates_polynomial {κ : ℕ} (input : List ℤ)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State 24} {t : ℕ}
    (hr : Runs (width κ input.length) ((program κ).program packedLen)
      (State.init (input.map Signed.encode)) s t) :
    (∀ i, s.data.regs i < (input.length + 2) ^ (40 * κ + 242)) ∧
      ∀ a, s.data.mem a < (input.length + 2) ^ (40 * κ + 242) := by
  have hpoly := two_pow_width_le κ input.length
  have hb := hr.bounded_init (inputFits input le_rfl hvalues)
  exact ⟨fun i => (hb.1 i).trans_le hpoly, fun a => (hb.2 a).trans_le hpoly⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters
