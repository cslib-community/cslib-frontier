/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Computability.WordRAM.CountingLoop
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Foundations.Data.BitString.Parity
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Foundations.Data.BitString.ListParity
import CslibFrontier.Foundations.Data.Nat.Bitwise.Projection
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Framed Word-RAM evaluators for the `4n - 9d` refuter

The refuter of issue `#4322` (Milestone 4) evaluates the hard function `f : BitString n → Bool`
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
certificate `exec` holds at every word width `w ≥ n + 1`, for every point `x`, every base
address `b` with `Fits w (b + space)`, and every data whose register `inp` holds `pointWord x`
and register `base` holds `b`; the other registers and all memory, including the workspace
window `[b, b + space)`, are arbitrary. From such data `code` runs within `cost` instructions to
data with `(f x).toNat` in `out`, registers `inp` and `base` unchanged, and every memory cell
outside the window unchanged. Window cells and the other registers are left unspecified.

The admitted widths are fixed rather than chosen by the evaluator: every `w ≥ n + 1`, the
widths at which the packed point fits and, even for `n = 0`, so does the constant `1`. A caller
may run at any larger width its own addresses need. The workspace is at most the cost
(`space_le_cost`), as a call of `cost` instructions touches at most `cost` cells. An evaluator
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
representation invariant and zero-fills its block before setup (`initClear`), an evaluator keeps
no state between calls and starts from dirty memory without any reset pass. It also differs from
`Program.ComputesInTime`, which certifies a flat program started from an input list at
caller-chosen admitted widths: an evaluator is a structured `Code` run inside a caller's
registers and memory, so its certificate carries a frame and starts from arbitrary data.

**Calls.** A caller runs `code` in an injective register bank `g` of its own register file
(`Code.rename`). `FramedEvaluator.exec_rename` gives the call postcondition `CallPost`: the
result in `g out`, `g inp` and `g base` kept, every caller register outside the bank kept and
memory outside the window kept, within `cost`. `FramedEvaluator.exec_loop` runs a counting loop
whose body is a charged preparation, one call and a charged continuation: from index `i₀` up
to the limit `N` it costs `(N - i₀) * (tPrep + cost + tCont + 2) + 2` instructions, overhead
plus the number of calls times the cost of evaluation and setup.

**Instance.** `parityEvaluator n` evaluates `Cslib.parity n` by a shift-and-mask loop over the
`n` bits of the packed point, with no workspace, at the widths `w ≥ n + 1`, within `6 n + 6`
instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.pointWord`, `fits_pointWord`: the packed word of a point
  and its fit.
* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator`: a fixed Word-RAM program for `f` with
  its calling convention, cost and execution certificate.
* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator.CallPost`: the postcondition of one call
  in a caller's register bank.
* `Cslib.Algorithms.WordRAM.Refuter4n.parityCode`, `parityEvaluator`: the parity instance.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator.exec_rename`: one call in a caller's
  register bank, within `cost`.
* `Cslib.Algorithms.WordRAM.Refuter4n.FramedEvaluator.exec_loop`: a counting loop with one call
  per iteration, every call charged.
* `Cslib.Algorithms.WordRAM.Refuter4n.exec_parityCode`: the certificate of the parity instance.
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

/-- A **framed Word-RAM evaluator** for `f : BitString n → Bool`: a fixed standard-basis program
on `r` registers with its calling convention and per-call instruction bound. The certificate
`exec` holds at every width `w ≥ n + 1`, from any data whose register `inp` holds the packed
point and register `base` the workspace base `b`, with all other registers and all memory
arbitrary (the window `[b, b + space)` included). It computes `(f x).toNat` into `out` within
`cost` instructions, keeps `inp` and `base`, and keeps every memory cell outside the window. -/
structure FramedEvaluator (n : ℕ) (f : BitString n → Bool) (r : ℕ) where
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
  /-- The execution certificate, for every width `w ≥ n + 1`, point, base and data. -/
  exec : ∀ {w b : ℕ} (x : BitString n) (s : Data r), n + 1 ≤ w → Fits w (b + space) →
    s.regs inp = pointWord x → s.regs base = b →
    ∃ t, ExecWithin w code s t cost ∧ t.regs out = (f x).toNat ∧
      t.regs inp = s.regs inp ∧ t.regs base = s.regs base ∧
      ∀ a, (a < b ∨ b + space ≤ a) → t.mem a = s.mem a

namespace FramedEvaluator

variable {f : BitString n → Bool} {r r' : ℕ} (E : FramedEvaluator n f r)

/-- The postcondition of one call of `E` in the register bank `g` of a caller, from caller data
`s` on the point `x` to caller data `t`: the result is in `g E.out`, the registers `g E.inp`
and `g E.base` are kept, every caller register outside the bank is kept, and every memory cell
outside the window at the base held in `g E.base` is kept. -/
@[expose] def CallPost (g : Fin r → Fin r') (x : BitString n) (s t : Data r') : Prop :=
  t.regs (g E.out) = (f x).toNat ∧ t.regs (g E.inp) = s.regs (g E.inp) ∧
    t.regs (g E.base) = s.regs (g E.base) ∧ (∀ i, (∀ j, g j ≠ i) → t.regs i = s.regs i) ∧
    ∀ a, (a < s.regs (g E.base) ∨ s.regs (g E.base) + E.space ≤ a) → t.mem a = s.mem a

/-- **One call in a caller's register bank.** If the caller's register `g E.inp` holds the packed
point `x` and the window at the base held in `g E.base` fits, the renamed program runs within
`E.cost` instructions and establishes `CallPost`. -/
theorem exec_rename {g : Fin r → Fin r'} (hg : g.Injective) {w : ℕ} (x : BitString n)
    (s : Data r') (hw : n + 1 ≤ w) (hfit : Fits w (s.regs (g E.base) + E.space))
    (hx : s.regs (g E.inp) = pointWord x) :
    ∃ t, ExecWithin w (E.code.rename g) s t E.cost ∧ E.CallPost g x s t := by
  obtain ⟨t, ht, ⟨hout, hinp, hbase, hmem⟩, hframe⟩ := ExecWithin.rename_post hg
    (E.exec x (s.comap g) hw hfit hx rfl)
  exact ⟨t, ht, hout, hinp, hbase, hframe, hmem⟩

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
    obtain ⟨t, ht, hpost⟩ := E.exec_rename hg x a hw hfit hx
    obtain ⟨z, hz, hP⟩ := hcont t hpost
    exact ⟨z, (hprep.seq (ht.seq hz)).mono (by omega), hP⟩) hle hs

end FramedEvaluator

/-! ### Instance: parity -/

section Parity

/-- Input register: the packed point. -/
private abbrev pInp : Fin 7 := 0
/-- Workspace base register (unused: the parity code has no workspace). -/
private abbrev pBase : Fin 7 := 1
/-- Result register: the running parity. -/
private abbrev pOut : Fin 7 := 2
/-- Bit counter. -/
private abbrev pI : Fin 7 := 3
/-- Bit count `n`. -/
private abbrev pLim : Fin 7 := 4
/-- Scratch register. -/
private abbrev pT : Fin 7 := 5
/-- Constant one. -/
private abbrev pOne : Fin 7 := 6

/-- One loop iteration: exclusive-or bit `i` of the input into the result. -/
private def parityBody : Code .standard 7 := ram[
  pT ← pInp >>> pI; pT ← pT &&& pOne; pOut ← pOut ^^^ pT; pI ← pI + pOne ]

/-- The parity evaluator's program: the exclusive or of bits `0, …, n - 1` of register `0` into
register `2`, with registers `3` to `6` as scratch. -/
def parityCode (n : ℕ) : Code .standard 7 :=
  .seq (ram[ pOut ← #0; pI ← #0; pLim ← #n; pOne ← #1 ]) (.loop (.lt pI pLim) parityBody)

private theorem toNat_xor (a b : Bool) : a.toNat ^^^ b.toNat = (a ^^ b).toNat := by
  cases a <;> cases b <;> rfl

private theorem exec_parityBody {w : ℕ} (y : Data 7) (hone : y.regs pOne = 1)
    (hi : Fits w (y.regs pI + 1)) (hinp : Fits w (y.regs pInp)) (h1 : Fits w 1) (b : Bool)
    (hout : y.regs pOut = b.toNat) :
    ∃ z, ExecWithin w parityBody y z 4 ∧ z.mem = y.mem ∧
      z.regs pI = y.regs pI + 1 ∧
      z.regs pOut = (b ^^ (y.regs pInp).testBit (y.regs pI)).toNat ∧
      z.regs pInp = y.regs pInp ∧ z.regs pBase = y.regs pBase ∧ z.regs pLim = y.regs pLim ∧
      z.regs pOne = y.regs pOne := by
  have hs : Fits w (y.regs pInp >>> y.regs pI) := hinp.of_le (Nat.shiftRight_le _ _)
  have hb : ∀ c : Bool, Fits w c.toNat := fun c => h1.of_le (Bool.toNat_le c)
  refine WP.exists_execWithin ?_
  unfold parityBody
  wram_exec [hone, hout, hs, hi, Nat.shiftRight_and_one, toNat_xor, hb]
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp⟩

/-- **The parity evaluator's certificate.** At every width `w ≥ n + 1`, from any data with the
packed point `pointWord x` in register `0`, `parityCode n` leaves `(parity n x).toNat` in
register `2` within `6 n + 6` instructions, keeps registers `0` and `1`, and keeps all memory. -/
theorem exec_parityCode {w : ℕ} (x : BitString n) (s : Data 7) (hw : n + 1 ≤ w)
    (hx : s.regs 0 = pointWord x) :
    ∃ t, ExecWithin w (parityCode n) s t (6 * n + 6) ∧ t.regs 2 = (parity n x).toNat ∧
      t.regs 0 = s.regs 0 ∧ t.regs 1 = s.regs 1 ∧ t.mem = s.mem := by
  have h1 : Fits w 1 := fits_one (by omega)
  have hn : Fits w n := (fits_self w).of_le (by omega)
  have hinp : Fits w (s.regs pInp) := hx ▸ fits_pointWord x (by omega)
  let P (k : ℕ) (z : Data 7) : Prop :=
    z.regs pInp = s.regs pInp ∧ z.regs pBase = s.regs pBase ∧ z.regs pLim = n ∧
      z.regs pOne = 1 ∧ z.mem = s.mem ∧
        z.regs pOut = (wordParity ((List.ofFn x).take k)).toNat
  have hbody (y : Data 7) (hy : P (y.regs pI) y) (hlt : y.regs pI < n) :
      ∃ z, ExecWithin w parityBody y z 4 ∧ P (y.regs pI + 1) z ∧
        z.regs pI = y.regs pI + 1 := by
    obtain ⟨hyi, hyb, hyl, hyo, hym, hyout⟩ := hy
    obtain ⟨z, he, hzm, hzi, hzout, hzinp, hzb, hzl, hzo⟩ := exec_parityBody y hyo
      (hn.of_le (by omega)) (hyi ▸ hinp) h1 _ hyout
    refine ⟨z, he, ⟨hzinp.trans hyi, hzb.trans hyb, hzl.trans hyl, hzo.trans hyo,
      hzm.trans hym, ?_⟩, hzi⟩
    rw [hzout, hyi, hx, testBit_equivFin x ⟨_, hlt⟩, List.take_add_one, List.getElem?_ofFn,
      wordParity_eq_sum, wordParity_eq_sum, List.sum_append]
    simp [hlt, Bool.add_eq_xor]
  refine WP.exists_execWithin ?_
  unfold parityCode
  wram_exec [hn, h1]
  wram_call (ExecWithin.loop_count P (fun _ ⟨_, _, hl, _⟩ => hl) hbody (by wram_simp; omega)
    ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp; simp⟩)
    with z ⟨⟨hzi, hzb, -, -, hzm, hzout⟩, -⟩
  refine ⟨by wram_simp; omega, ?_, hzi, hzb, hzm⟩
  rw [hzout, List.take_of_length_le (by simp), wordParity_ofFn]
  rfl

/-- **The parity evaluator**: `parityCode n` as a framed evaluator for `Cslib.parity n`, with the
point in register `0`, the (unused) base in register `1`, the result in register `2`, no
workspace, at the widths `w ≥ n + 1`, within `6 n + 6` instructions per call. -/
@[expose] def parityEvaluator (n : ℕ) : FramedEvaluator n (parity n) 7 where
  code := parityCode n
  inp := 0
  base := 1
  out := 2
  space := 0
  cost := 6 * n + 6
  inp_ne_base := by decide
  space_le_cost := Nat.zero_le _
  exec x s hw _ hx _ := by
    obtain ⟨t, ht, hout, hinp, hbase, hmem⟩ := exec_parityCode x s hw hx
    exact ⟨t, ht, hout, hinp, hbase, fun a _ => by rw [hmem]⟩

end Parity

end Cslib.Algorithms.WordRAM.Refuter4n
