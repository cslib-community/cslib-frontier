/-
Copyright (c) 2026 Christian Reitwiessner, Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Ryan Anderson
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.Evaluator
public meta import CslibFrontier.Algorithms.WordRAM.Refuter4n.Evaluator

/-!
# Tests for framed Word-RAM evaluators

* `evalMany E`: a generic caller of a framed evaluator `E`. It evaluates `f` on `k` packed points
  stored at `[src, src + k)` and writes the results to `[dst, dst + k)`, through
  `FramedEvaluator.exec_loop`, within `k * (E.cost + 7) + 4` instructions: every call charged.
  Memory outside the window and the output block is kept (`exec_evalMany`).
* `exec_evalMany` instantiated with `parityEvaluator` as an ordinary module client.
* Runs of the interpreter `Code.eval` on `parityCode n` and on `evalMany (parityEvaluator n)`
  for concrete points, with dirty memory and registers: results and instruction counts within
  the proved bounds.
-/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.Refuter4nEvaluator

open Cslib Cslib.BitString Cslib.WordRAM Cslib.Algorithms.WordRAM.Refuter4n

variable {n r : ℕ} {f : BooleanFunction n}

/-! ### A generic caller: evaluate `f` on `k` stored points -/

/-- The caller's registers `r + 0, …, r + 5`: index, count, source base, destination base,
address scratch and the constant one. The evaluator runs in registers `0, …, r - 1`. -/
@[simp] abbrev cK (r : ℕ) : Fin (r + 6) := Fin.natAdd r 0
@[simp] abbrev cCnt (r : ℕ) : Fin (r + 6) := Fin.natAdd r 1
@[simp] abbrev cSrc (r : ℕ) : Fin (r + 6) := Fin.natAdd r 2
@[simp] abbrev cDst (r : ℕ) : Fin (r + 6) := Fin.natAdd r 3
@[simp] abbrev cA (r : ℕ) : Fin (r + 6) := Fin.natAdd r 4
@[simp] abbrev cOne (r : ℕ) : Fin (r + 6) := Fin.natAdd r 5

/-- The evaluator's bank in the caller. -/
abbrev bank (r : ℕ) : Fin r → Fin (r + 6) := Fin.castAdd 6

/-- Load point `k` into the evaluator's input register. -/
def evalPrep (E : FramedEvaluator n f r) : Code .standard (r + 6) :=
  .seq (.op (.bin .add (cA r) (cSrc r) (cK r))) (.op (.load (bank r E.inp) (cA r)))

/-- Store the result at `dst + k` and advance `k`. -/
def evalCont (E : FramedEvaluator n f r) : Code .standard (r + 6) :=
  .seq (.op (.bin .add (cA r) (cDst r) (cK r)))
    (.seq (.op (.store (cA r) (bank r E.out))) (.op (.bin .add (cK r) (cK r) (cOne r))))

/-- Evaluate `f` on the `k` points at `[src, src + k)` into `[dst, dst + k)`. -/
def evalMany (E : FramedEvaluator n f r) : Code .standard (r + 6) :=
  .seq (.seq (.op (.const (cK r) 0)) (.op (.const (cOne r) 1)))
    (.loop (.lt (cK r) (cCnt r)) (.seq (evalPrep E) (.seq (E.code.rename (bank r)) (evalCont E))))

@[simp] private theorem bank_ne (i : Fin r) (j : Fin 6) : bank r i ≠ Fin.natAdd r j :=
  fun h => by
    have := congrArg Fin.val h
    simp only [bank, Fin.val_castAdd, Fin.val_natAdd] at this
    omega

@[simp] private theorem ne_bank (i : Fin r) (j : Fin 6) : Fin.natAdd r j ≠ bank r i :=
  (bank_ne i j).symm

/-- The window `[b, b + space)` misses the address `a`. -/
abbrev Outside (b space a : ℕ) : Prop := a < b ∨ b + space ≤ a

/-- **A generic caller charges every call.** Let the caller's data hold `k` in its count
register, `src` and `dst` in its base registers and `b` in the evaluator's base register, with
the packed point `xs[j]` at `src + j`. If the source block, the output block and the window
`[b, b + space)` are pairwise disjoint and all addresses fit, then `evalMany E` writes
`(f xs[j]).toNat` at `dst + j` for every `j < k` within `k * (E.cost + 7) + 4` instructions, and
keeps every cell outside the window and the output block. -/
theorem exec_evalMany (E : FramedEvaluator n f r) {w b src dst : ℕ} (xs : List (BitString n))
    (s : Data (r + 6)) (hw : n + 1 ≤ w) (hcnt : s.regs (cCnt r) = xs.length)
    (hsrc : s.regs (cSrc r) = src) (hdst : s.regs (cDst r) = dst)
    (hb : s.regs (bank r E.base) = b)
    (hpts : ∀ (j : ℕ) (hj : j < xs.length), s.mem (src + j) = pointWord xs[j])
    (hfb : Fits w (b + E.space)) (hfs : Fits w (src + xs.length))
    (hfd : Fits w (dst + xs.length))
    (hsw : ∀ j < xs.length, Outside b E.space (src + j))
    (hdw : ∀ j < xs.length, Outside b E.space (dst + j))
    (hsd : ∀ i < xs.length, ∀ j < xs.length, dst + i ≠ src + j) :
    ∃ t, ExecWithin w (evalMany E) s t (xs.length * (E.cost + 7) + 4) ∧
      (∀ (j : ℕ) (hj : j < xs.length), t.mem (dst + j) = (f xs[j]).toNat) ∧
      ∀ a, Outside b E.space a → (a < dst ∨ dst + xs.length ≤ a) → t.mem a = s.mem a := by
  have h1 : Fits w 1 := fits_one (by omega)
  have hib := E.inp_ne_base
  let P (k : ℕ) (z : Data (r + 6)) : Prop :=
    z.regs (cCnt r) = xs.length ∧ z.regs (cSrc r) = src ∧ z.regs (cDst r) = dst ∧
      z.regs (cOne r) = 1 ∧ z.regs (bank r E.base) = b ∧
      (∀ (j : ℕ) (hj : j < xs.length), j < k → z.mem (dst + j) = (f xs[j]).toNat) ∧
      ∀ a, Outside b E.space a → (a < dst ∨ dst + k ≤ a) → z.mem a = s.mem a
  -- setup
  let s₀ : Data (r + 6) := (s.set (cK r) 0).set (cOne r) 1
  have he₀ : ExecWithin (B := .standard) w
      (.seq (.op (.const (cK r) 0)) (.op (.const (cOne r) 1))) s s₀ 2 :=
    (Exec.const (fits_zero w)).within.seq (Exec.const h1).within
  have hk₀ : s₀.regs (cK r) = 0 := by simp [s₀]
  have hP₀ : P (s₀.regs (cK r)) s₀ := by
    rw [hk₀]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun j _ hj => absurd hj (Nat.not_lt_zero j), fun a _ _ => rfl⟩ <;>
      simp [s₀, hcnt, hsrc, hdst, hb]
  have hstep (y : Data (r + 6)) (hy : P (y.regs (cK r)) y) (hlt : y.regs (cK r) < xs.length) :
      ∃ a x, ExecWithin w (evalPrep E) y a 2 ∧
        Fits w (a.regs (bank r E.base) + E.space) ∧ a.regs (bank r E.inp) = pointWord x ∧
        ∀ t, E.CallPost (bank r) x a t → ∃ z, ExecWithin w (evalCont E) t z 3 ∧
          P (y.regs (cK r) + 1) z ∧ z.regs (cK r) = y.regs (cK r) + 1 := by
    obtain ⟨hyc, hys, hyd, hyo, hyb, hyres, hyfr⟩ := hy
    obtain ⟨k, hk⟩ : ∃ k, y.regs (cK r) = k := ⟨_, rfl⟩
    rw [hk] at hlt hyres hyfr ⊢
    have hsrcf : Fits w (y.regs (cSrc r) + y.regs (cK r)) := by
      rw [hys, hk]; exact hfs.of_le (by omega)
    have hsk : y.mem (src + k) = pointWord xs[k] := by
      rw [hyfr _ (hsw k hlt) ?_, hpts k hlt]
      by_contra hc
      exact hsd (src + k - dst) (by omega) k hlt (by omega)
    refine ⟨_, xs[k], ((Exec.bin hsrcf).within.seq Exec.load.within), ?_, ?_, ?_⟩
    · simpa [Function.update_apply, Ne.symm hib, hyb] using hfb
    · simp [hys, hk, hsk]
    intro t ⟨hout, _, hbase, hregs, hmem⟩
    have hta (i : Fin 6) (hi : i ≠ 4) : t.regs (Fin.natAdd r i) = y.regs (Fin.natAdd r i) := by
      rw [hregs _ fun j => bank_ne j i]
      simp [hi]
    have htb : t.regs (bank r E.base) = b := by
      rw [hbase]
      simpa [Function.update_apply, Ne.symm hib] using hyb
    have htm : ∀ a, Outside b E.space a → t.mem a = y.mem a := fun a ha => by
      rw [hmem a (by simpa [Function.update_apply, Ne.symm hib, hyb] using ha)]
      rfl
    have htd : t.regs (cDst r) = dst := (hta 3 (by decide)).trans hyd
    have htk : t.regs (cK r) = k := (hta 0 (by decide)).trans hk
    have hto : t.regs (cOne r) = 1 := (hta 5 (by decide)).trans hyo
    have htc : t.regs (cCnt r) = xs.length := (hta 1 (by decide)).trans hyc
    have hts : t.regs (cSrc r) = src := (hta 2 (by decide)).trans hys
    have hdk : Fits w (t.regs (cDst r) + t.regs (cK r)) := by
      rw [htd, htk]; exact hfd.of_le (by omega)
    have hk1 : Fits w (k + 1) := hfs.of_le (by omega)
    refine ⟨_, (Exec.bin hdk).within.seq (Exec.store.within.seq (Exec.bin ?_).within),
      ⟨?_, ?_, ?_, ?_, ?_, fun j hj hjk => ?_, fun a ha had => ?_⟩, ?_⟩
    · simpa [Function.update_apply, htk, hto] using hk1
    · simpa [Function.update_apply] using htc
    · simpa [Function.update_apply] using hts
    · simpa [Function.update_apply] using htd
    · simpa [Function.update_apply] using hto
    · simpa [Function.update_apply] using htb
    · simp only [Data.set_mem, Data.write_mem, Data.set_regs, Function.update_self, cA,
        BinOp.eval, htd, htk]
      by_cases hjk' : j = k
      · subst hjk'
        simpa [Function.update_apply] using hout
      · rw [Function.update_of_ne (by omega), htm _ (hdw j hj), hyres j hj (by omega)]
    · simp only [Data.set_mem, Data.write_mem, Data.set_regs, Function.update_self, cA,
        BinOp.eval, htd, htk]
      rw [Function.update_of_ne (by omega), htm a ha, hyfr a ha (by omega)]
    · simp [htk, hto]
  obtain ⟨y, hy, hP, -⟩ := E.exec_loop (g := bank r) (Fin.castAdd_injective r 6) hw
    (tPrep := 2) (tCont := 3) (index := cK r) (limit := cCnt r) (prep := evalPrep E)
    (cont := evalCont E) P (fun y hy => hy.1) hstep (by rw [hk₀]; omega) hP₀
  obtain ⟨-, -, -, -, -, hres, hfr⟩ := hP
  refine ⟨y, (he₀.seq hy).mono (le_of_eq ?_), fun j hj => hres j hj hj, hfr⟩
  rw [hk₀, Nat.sub_zero]
  ring

/-! ### The parity instance -/

/-- The certificate of `parityEvaluator 4` at width `5`, as an ordinary module client. -/
example (x : BitString 4) (s : Data 7) (hx : s.regs 0 = pointWord x) (hb : s.regs 1 = 0) :
    ∃ t, ExecWithin 5 (parityEvaluator 4).code s t 30 ∧ t.regs 2 = (parity 4 x).toNat ∧
      t.mem 9 = s.mem 9 := by
  obtain ⟨t, ht, hout, -, -, hmem⟩ := (parityEvaluator 4).exec (w := 5) (b := 0) x s
    (show 4 + 1 ≤ 5 by decide) (by simp [parityEvaluator, Fits]) hx hb
  exact ⟨t, ht, hout, hmem 9 (by simp [parityEvaluator])⟩

/-- `FramedEvaluator.exec_rename` for the parity evaluator in the bank of `evalMany`: the result
lands in caller register `2`, and a caller register outside the bank is kept. -/
example (x : BitString 3) (s : Data 13) (hx : s.regs 0 = pointWord x) (hb : s.regs 1 = 0) :
    ∃ t, ExecWithin 4 ((parityEvaluator 3).code.rename (bank 7)) s t 24 ∧
      t.regs 2 = (parity 3 x).toNat ∧ t.regs (cSrc 7) = s.regs (cSrc 7) := by
  have hfit : Fits 4 (s.regs 1 + 0) := by rw [hb]; decide
  obtain ⟨t, ht, hout, -, -, hregs, -⟩ := (parityEvaluator 3).exec_rename
    (Fin.castAdd_injective 7 6) x s (show 3 + 1 ≤ 4 by decide) hfit hx
  exact ⟨t, ht, hout, hregs _ fun j => bank_ne j 2⟩

/-- `exec_evalMany` for the parity evaluator: `k` calls charged `k * (6 n + 13) + 4`. -/
example {w b src dst : ℕ} (xs : List (BitString 3)) (s : Data 13) (hw : 4 ≤ w)
    (hcnt : s.regs 8 = xs.length) (hsrc : s.regs 9 = src) (hdst : s.regs 10 = dst)
    (hb : s.regs 1 = b) (hpts : ∀ (j : ℕ) (hj : j < xs.length), s.mem (src + j) = pointWord xs[j])
    (hfb : Fits w b) (hfs : Fits w (src + xs.length)) (hfd : Fits w (dst + xs.length))
    (hsd : ∀ i < xs.length, ∀ j < xs.length, dst + i ≠ src + j) :
    ∃ t, ExecWithin w (evalMany (parityEvaluator 3)) s t (xs.length * 31 + 4) ∧
      ∀ (j : ℕ) (hj : j < xs.length), t.mem (dst + j) = (parity 3 xs[j]).toNat := by
  obtain ⟨t, ht, hres, -⟩ := exec_evalMany (parityEvaluator 3) xs s hw hcnt hsrc hdst
    hb hpts (by simpa [parityEvaluator] using hfb) hfs hfd
    (fun j _ => show src + j < b ∨ b + 0 ≤ src + j by omega)
    (fun j _ => show dst + j < b ∨ b + 0 ≤ dst + j by omega)
    hsd
  exact ⟨t, ht, hres⟩

/-- A point of `BitString n` from the low bits of `v`. -/
def ofWord (n v : ℕ) : BitString n := fun i => v.testBit i

/-- Dirty data: the packed point `v` in register `0`, base `20` in register `1`, junk elsewhere. -/
def dirty (v : ℕ) : Data 7 :=
  ⟨fun i => if i = 0 then v else if i = 1 then 20 else 17 * i.val + 3, fun a => 7 * a + 1⟩

/-- Run `parityCode n` at width `n + 1` on `ofWord n v`: the result is the parity, registers `0`
and `1` are kept, memory is kept at a few addresses, and the count is within `6 n + 6`. -/
def parityOk (n v : ℕ) : Bool :=
  let x := ofWord n v
  match (parityCode n).eval (n + 1) 1000 (dirty (pointWord x)) with
  | some (y, t) =>
    y.regs 2 == (parity n x).toNat && y.regs 0 == pointWord x && y.regs 1 == 20 &&
      ((List.range 30).all fun a => y.mem a == 7 * a + 1) && t ≤ 6 * n + 6
  | none => false

#guard (List.range 2).all (parityOk 0)
#guard (List.range 8).all (parityOk 3)
#guard (List.range 64).all (parityOk 6)

/-- Caller data for `evalMany (parityEvaluator n)`: `k` points from `vs` at `src = 40`, output at
`dst = 60`, base `0`, junk elsewhere. -/
def callerData (n : ℕ) (vs : List ℕ) : Data 13 :=
  ⟨fun i => if i = 8 then vs.length else if i = 9 then 40 else if i = 10 then 60
      else if i = 1 then 0 else 5 * i.val + 2,
    fun a => if 40 ≤ a ∧ a < 40 + vs.length then pointWord (ofWord n (vs.getD (a - 40) 0))
      else 3 * a + 11⟩

/-- Run `evalMany (parityEvaluator n)` at width `12`: every output is the parity of its point,
memory outside the output block is kept, and the count is within `k * (cost + 7) + 4`. -/
def manyOk (n : ℕ) (vs : List ℕ) : Bool :=
  let s := callerData n vs
  match (evalMany (parityEvaluator n)).eval 12 1000 s with
  | some (y, t) =>
    ((List.range vs.length).all fun j =>
        y.mem (60 + j) == (parity n (ofWord n (vs.getD j 0))).toNat) &&
      ((List.range 100).all fun a => (60 ≤ a ∧ a < 60 + vs.length) || y.mem a == s.mem a) &&
      t ≤ vs.length * ((parityEvaluator n).cost + 7) + 4
  | none => false

#guard manyOk 3 []
#guard manyOk 3 [0, 1, 2, 3, 4, 5, 6, 7]
#guard manyOk 5 [31, 17, 8, 0, 21]

end CslibFrontierTests.Refuter4nEvaluator
