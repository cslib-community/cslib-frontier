/-
Copyright (c) 2026 Christian Reitwiessner, Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.Structured
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Framed Word-RAM evaluators for the `4n - 9d` refuter

The refuter of issue `#4322` (Milestone 4) evaluates the hard function `f : BooleanFunction n`
on its candidate points. The Word-RAM has no oracle instruction, so `f` is given as code. This
module states the contract such code must meet, in the library's Word-RAM cost model, and how a
caller charges its calls. No running time is claimed for the refuter here, and no
polynomial-time instantiation: adapting `ComputableInPolyTime.exists_wordRAM` (a flat program on
bit-per-word inputs) to this calling convention is separate work.

**Packed input.** A point `x : BitString n` is passed as one word, `pointWord x`, its number in
the existing `BitString.equivFin n` (an abbreviation naming the calling convention, so the
`equivFin` lemmas such as `testBit_equivFin` apply to it directly). The word is below `2 ^ n`,
so it fits at every width `w ≥ n` (`fits_pointWord`).

**Contract.** A `FramedEvaluator n f r` is a fixed standard-basis program `code` on `r`
registers, with an input register `inp`, a workspace base register `base`, a result register
`out` (`inp ≠ base`), a workspace size `space` and a per-call instruction bound `cost`. The
certificate `exec` holds at every word width `w ≥ n + 1`, for every point `x` and every data
whose register `inp` holds `pointWord x` and whose register `base` holds an address `b` with
`Fits w (b + space)`; the other registers and all memory, including the workspace window
`[b, b + space)`, are arbitrary. From such data `code` runs within `cost` instructions to data
satisfying `EvalPost`: `(f x).toNat` in `out`, registers `inp` and `base` unchanged, and every
memory cell outside the window unchanged. Window cells and the other registers are left
unspecified.

The admitted widths are fixed rather than chosen by the evaluator: every `w ≥ n + 1`, the
widths at which the packed point fits and, even for `n = 0`, so does the constant `1`. A caller
may run at any larger width its own addresses need. The workspace is at most the cost
(`space_le_cost`), the usual space-within-time bound (a call of `cost` instructions accesses at
most `cost` cells, though not necessarily contiguous ones). An evaluator
that could choose its widths could hide a `2 ^ n`-bit truth table of `f` in one constant and
answer within a constant `cost`; with these two conditions it must either work at width `n + 1`
or have a window that does not fit there, and then pay `cost ≥ space ≥ 2 ^ (n + 1)` per call.
The code itself is not bounded in length, so for one `n` a branching program over the bits gives
cost `O(n)` for every `f`; uniformity in `n` is the role of the polynomial-time instantiation,
which stays open.

Since the certificate starts from arbitrary window contents and scratch registers, a call needs
no reset before it, and any initialisation the code performs is part of `cost`: every call,
with its setup, is charged by `cost`. Since memory outside the window is arbitrary and the result
is fixed, the result cannot depend on it; since it is preserved, so is any refuter state stored
there. This is a stateless calling convention: unlike `SubroutineBase`, which carries a
representation invariant and whose dirty-memory initializer `initClear` zero-fills its block, an
evaluator keeps no state between calls and starts from dirty memory without any reset pass. It
also differs from `Program.ComputesInTime`, which certifies a flat program started from an input
list at the admitted widths its statement names: an evaluator is a structured `Code` run inside
a caller's registers and memory, so its certificate carries a frame and starts from arbitrary
data.

**Calls.** A caller runs `code` in an injective register bank `g` of its own register file
(`Code.rename`). The call postcondition `CallPost` is `EvalPost` read through the bank, plus
every caller register outside the bank kept.
`FramedEvaluator.exec_loop` runs a counting loop whose body is a charged preparation, one call
and a charged continuation (`ExecWithin.call`): from index `i₀` up to the limit `N` it costs
`(N - i₀) * (tPrep + cost + tCont + 2) + 2` instructions, overhead plus the number of calls
times the cost of evaluation and setup.

**Instances.** Witnesses of the contract live in the tests
(`CslibFrontierTests.Refuter4nEvaluator`): a parity evaluator with no workspace and an
evaluator with a one-cell window.

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.pointWord`: the packed word of a point.
* `Cslib.Algorithms.WordRAM.Refuter4n.EvalPost`: the postcondition of one evaluation.
* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator`: a fixed Word-RAM program for `f` with
  its calling convention, cost and execution certificate.
* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator.CallPost`: the postcondition of one call
  in a caller's register bank.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator.exec_loop`: a counting loop with one call
  per iteration, every call charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Cslib.WordRAM Cslib.BitString

variable {n : ℕ}

/-! ### Packed points -/

/-- The packed word of a point: its number in `BitString.equivFin n`, with `x i` at bit `i`
(`testBit_equivFin`). -/
abbrev pointWord (x : BitString n) : ℕ := (equivFin n x : ℕ)

/-- The packed word of a point fits at every width `w ≥ n`. -/
theorem fits_pointWord {w : ℕ} (x : BitString n) (h : n ≤ w) : Fits w (pointWord x) :=
  Fits.mono (equivFin n x).isLt h

/-! ### The evaluator contract -/

/-- The postcondition of one evaluation of `f` on `x`, from data `s` to data `t`, for the input
register `inp`, the base register `base`, the result register `out` and a window of `space`
cells at the base held in `base`. The memory frame is `Modifies` on the window's
`Block.footprint` (`Modifies.block_iff` gives it cell by cell). -/
structure EvalPost {r : ℕ} (f : BooleanFunction n) (inp base out : Fin r) (space : ℕ)
    (x : BitString n) (s t : Data r) : Prop where
  /-- The result register holds `(f x).toNat`. -/
  result : t.regs out = (f x).toNat
  /-- The input register is kept. -/
  inp_eq : t.regs inp = s.regs inp
  /-- The base register is kept. -/
  base_eq : t.regs base = s.regs base
  /-- Every memory cell outside the window is kept. -/
  mem_eq : Modifies (Block.mk (s.regs base) space).footprint s.mem t.mem

/-- A **framed Word-RAM evaluator** for `f : BooleanFunction n`: a fixed standard-basis program
on `r` registers with its calling convention and per-call instruction bound. The certificate
`exec` holds at every width `w ≥ n + 1`, from any data whose register `inp` holds the packed
point and register `base` a workspace base `b` with `Fits w (b + space)`, with all other
registers and all memory arbitrary (the window `[b, b + space)` included). It computes
`(f x).toNat` into `out` within `cost` instructions, keeps `inp` and `base`, and keeps every
memory cell outside the window (`EvalPost`). -/
structure FramedEvaluator (n : ℕ) (f : BooleanFunction n) (r : ℕ) where
  /-- The fixed program. -/
  code : Code .standard r
  /-- The register holding the packed point `pointWord x`. -/
  inp : Fin r
  /-- The register holding the base address `b` of the workspace window. -/
  base : Fin r
  /-- The register receiving `(f x).toNat`. -/
  out : Fin r
  /-- The size of the workspace window `[b, b + space)`. -/
  space : ℕ
  /-- The instruction bound of one call, setup and reset included. -/
  cost : ℕ
  /-- The input and base registers are distinct, so a caller can set both. -/
  inp_ne_base : inp ≠ base
  /-- The workspace is at most the cost, so a large window cannot raise the admitted widths for
  free. -/
  space_le_cost : space ≤ cost
  /-- The execution certificate, for every width `w ≥ n + 1`, point and data whose window at the
  base held in `base` fits. -/
  exec : ∀ {w : ℕ} (x : BitString n) (s : Data r), n + 1 ≤ w →
    Fits w (s.regs base + space) → s.regs inp = pointWord x →
    ∃ t, ExecWithin w code s t cost ∧ EvalPost f inp base out space x s t

namespace FramedEvaluator

variable {f : BooleanFunction n} {r r' : ℕ} (E : FramedEvaluator n f r)

/-- The postcondition of one call of `E` in the register bank `g` of a caller, from caller data
`s` on the point `x` to caller data `t`: `EvalPost` read through the bank (the result in
`g E.out`, `g E.inp` and `g E.base` kept, memory outside the window kept), and every caller
register outside the bank kept. -/
structure CallPost (g : Fin r → Fin r') (x : BitString n) (s t : Data r') : Prop
    extends EvalPost f E.inp E.base E.out E.space x (s.comap g) (t.comap g) where
  /-- Every caller register outside the bank is kept. -/
  regs_eq : ∀ i, (∀ j, g j ≠ i) → t.regs i = s.regs i

/-- **A counting loop with one call per iteration.** The body is a charged preparation `prep`,
one call of `E` in the bank `g` and a charged continuation `cont`, at a width `w ≥ n + 1`. At
each iteration below `N`, the preparation reaches data at which the call is admitted on some
point, and the continuation re-establishes the invariant at the next index from any data
satisfying `CallPost`. Then the loop runs within
`(N - i₀) * (tPrep + E.cost + tCont + 2) + 2` instructions from index `i₀`: every call and its
setup is charged. -/
theorem exec_loop {g : Fin r → Fin r'} (hg : g.Injective) {w N tPrep tCont : ℕ}
    (hw : n + 1 ≤ w) {index limit : Fin r'} {prep cont : Code .standard r'}
    (P : ℕ → Data r' → Prop)
    (hlimit : ∀ y, P (y.regs index) y → y.regs limit = N)
    (hstep : ∀ y, P (y.regs index) y → y.regs index < N →
      ∃ a x, ExecWithin w prep y a tPrep ∧ Fits w (a.regs (g E.base) + E.space) ∧
        a.regs (g E.inp) = pointWord x ∧
        ∀ t, E.CallPost g x a t → ∃ z, ExecWithin w cont t z tCont ∧
          P (y.regs index + 1) z ∧ z.regs index = y.regs index + 1)
    {s : Data r'} (hle : s.regs index ≤ N) (hs : P (s.regs index) s) :
    ∃ y, ExecWithin w (.loop (.lt index limit) (.seq prep (.seq (E.code.rename g) cont))) s y
      ((N - s.regs index) * (tPrep + E.cost + tCont + 2) + 2) ∧ P N y ∧ y.regs index = N :=
  ExecWithin.loop_count P hlimit (fun y hy hlt => by
    obtain ⟨a, x, hprep, hfit, hx, hcont⟩ := hstep y hy hlt
    exact ExecWithin.call hg hprep (E.exec x (a.comap g) hw hfit hx)
      fun t hpost hframe => hcont t ⟨hpost, hframe⟩) hle hs

end FramedEvaluator

end Cslib.Algorithms.WordRAM.Refuter4n
