/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Probability.Product

public import CslibFrontier.Init
public import Cslib.Probability.PMF
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Randomized.Law
public import Mathlib.Data.Fintype.Pi

/-!
# Acceptance observation and uniform bit-slice sampling on the randomized word RAM

Shared acceptance and bit-sampling primitives for randomized word-RAM algorithms:

* `Cslib.WordRAM.RandCfg.accepts`: whether a randomized machine configuration halted with output
  `1`.
* `Cslib.WordRAM.bitsAt`: reads `n` words from memory starting at `base` as a Boolean vector
  (`true` when the word is `1`).
* `Cslib.WordRAM.sampleBits`: register-parametric structured subroutine drawing `n` independent
  uniform bits via `rand one` into `[base, base + n)` in `6 * n + 3` instructions and `n` `rand`
  calls (`Cslib.WordRAM.sampleBits_law`), preserving memory outside `[base, base + n)` and all
  registers outside `{cnt, val, addr}`.
* `Cslib.WordRAM.Code.usesRandSrc` and `Cslib.WordRAM.ExecRand.queriesSatisfy_eq_of_usesRandSrc`:
  syntactic source-register check certifying `OracleComp.QueriesSatisfy` bounds (for example
  `RandBitsBounded` when every `rand` reads `one`).

## Main definitions

* `Cslib.WordRAM.RandCfg.accepts`: acceptance predicate on `RandCfg`.
* `Cslib.WordRAM.bitsAt`: Boolean vector read from a contiguous slice of words.
* `Cslib.WordRAM.sampleBits`: uniform bit-slice sampling subroutine on `Code .standard`.
* `Cslib.WordRAM.Code.usesRandSrc`: syntactic check that every `rand` reads a fixed register.

## Main results

* `Cslib.WordRAM.bitsAt_update_self`: writing at `base + i` updates coordinate `i` of `bitsAt`.
* `Cslib.WordRAM.sampleBits_law`: exact `PMF.uniformOfFintype (Fin n → Bool)` law, `6 * n + 3`
  instruction bound, `n`-call budget, and register/memory frame preservation for `sampleBits`.
* `Cslib.WordRAM.ExecRand.queriesSatisfy_eq_of_usesRandSrc`: every oracle query equals the constant
  held in a preserved `rand` source register.
-/

public section

namespace Cslib.WordRAM

open Cslib.Probability

variable {B : Basis} {r : ℕ}

/-! ### Acceptance observation on `RandCfg` -/

/-- Whether a randomized machine configuration halted with output `1`. -/
@[expose]
def RandCfg.accepts : RandCfg r → Bool
  | .halted v _ => decide (v = 1)
  | _ => false

@[simp]
theorem RandCfg.accepts_halted (v : ℕ) (d : Data r) :
    (RandCfg.halted v d).accepts = decide (v = 1) :=
  rfl

@[simp]
theorem RandCfg.accepts_running (s : State r) :
    (RandCfg.running s).accepts = false :=
  rfl

@[simp]
theorem RandCfg.accepts_faulted :
    (RandCfg.faulted : RandCfg r).accepts = false :=
  rfl

/-! ### Reading and sampling Boolean vectors -/

/-- Read `n` words starting at `base` as a Boolean vector (`true` when the word equals `1`). -/
@[expose]
def bitsAt (mem : ℕ → ℕ) (base n : ℕ) : Fin n → Bool :=
  fun i => decide (mem (base + i.val) = 1)

/-- Writing `v` at `base + i` updates coordinate `i` of `bitsAt mem base n`. -/
theorem bitsAt_update_self {n : ℕ} (mem : ℕ → ℕ) (base : ℕ) (i : Fin n) (v : ℕ) :
    bitsAt (Function.update mem (base + i.val) v) base n =
      Function.update (bitsAt mem base n) i (decide (v = 1)) := by
  funext j
  simp only [bitsAt, Function.update_apply, Nat.add_left_cancel_iff, Fin.ext_iff]
  split_ifs <;> rfl

private def sampleBitsBody (one baseReg cnt val addr : Fin r) : Code .standard r := ram[
  val ← rand one;
  addr ← baseReg + cnt;
  *addr ← val;
  cnt ← cnt + one ]

private def sampleBitsLoop (one baseReg nReg cnt val addr : Fin r) : Code .standard r :=
  .loop (.lt cnt nReg) (sampleBitsBody one baseReg cnt val addr)

/-- Sample `n = regs nReg` independent uniform bits via `rand one` into `[regs baseReg,
regs baseReg + n)`, using `cnt`, `val` and `addr` as scratch registers. -/
@[expose]
def sampleBits (zero one baseReg nReg cnt val addr : Fin r) : Code .standard r := ram[
  cnt ← zero;
  ⟪.loop (.lt cnt nReg) ram[
    val ← rand one;
    addr ← baseReg + cnt;
    *addr ← val;
    cnt ← cnt + one ]⟫ ]

@[simp]
theorem preserves_sampleBits {zero one baseReg nReg cnt val addr i : Fin r} :
    (sampleBits zero one baseReg nReg cnt val addr).Preserves i ↔
      i ≠ cnt ∧ i ≠ val ∧ i ≠ addr := by
  simp only [sampleBits, Code.Preserves, Op.dest, Op.bin, ne_eq,
    Option.some.injEq, reduceCtorEq, not_false_eq_true, @ne_comm _ _ i]
  tauto

private theorem sampleBitsLoop_law {w base n : ℕ}
    {one baseReg nReg cnt val addr : Fin r}
    (hdistinct : [one, baseReg, nReg, cnt, val, addr].Nodup)
    (hw1 : Fits w 1) (hw_end : Fits w (base + n)) :
    ∀ (d : ℕ) (x : Data r),
      x.regs one = 1 → x.regs baseReg = base → x.regs nReg = n →
      x.regs cnt + d = n →
      (∀ i < x.regs cnt, x.mem (base + i) ≤ 1) →
      ExecRandLaw w (sampleBitsLoop one baseReg nReg cnt val addr) x
        (fun y =>
          (∀ i < n, y.mem (base + i) ≤ 1) ∧
          (∀ a, ¬(base ≤ a ∧ a < base + n) → y.mem a = x.mem a) ∧
          ∀ i : Fin r, i ≠ cnt → i ≠ val → i ≠ addr → y.regs i = x.regs i)
        (6 * d + 2) d
        (fun y => bitsAt y.mem base n)
        ((PMF.uniformOfFintype (Fin n → Bool)).map fun τ i =>
          if i.val < x.regs cnt then bitsAt x.mem base n i else τ i)
  | 0, x, _, _, hn, hd, hbits => by
    have hc : ¬(Cond.lt cnt nReg).Holds x := by simp [Cond.holds_lt, hn]; omega
    have hi (i : Fin n) : i.val < x.regs cnt := by omega
    have hconst : (fun τ : Fin n → Bool => fun i : Fin n =>
        if i.val < x.regs cnt then bitsAt x.mem base n i else τ i) =
        Function.const _ (bitsAt x.mem base n) := by
      funext _ i
      simp only [Function.const_apply, hi, ↓reduceIte]
    rw [hconst, PMF.map_const]
    exact ExecRandLaw.loop_exit hc
      ⟨fun i hi => hbits i (by omega), fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | d + 1, x, ho, hbReg, hn, hd, hbits => by
    have hnd := hdistinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hdistinct
    obtain ⟨⟨-, -, hone_c, hone_v, hone_a⟩, ⟨-, hb_c, hb_v, hb_a⟩, ⟨hn_c, hn_v, hn_a⟩,
      ⟨hc_v, hc_a⟩, hv_a, -⟩ := hdistinct
    generalize hj : x.regs cnt = j at hd hbits ⊢
    have hjn : j < n := by omega
    have hc : (Cond.lt cnt nReg).Holds x := by simp [Cond.holds_lt, hn, hj]; omega
    have : Fits w (base + j) := hw_end.of_le (by omega)
    have : Fits w (j + 1) := hw_end.of_le (by omega)
    let Y (b : ℕ) : Data r :=
      (((x.set val b).set addr (base + j)).write (base + j) b).set cnt (j + 1)
    have hrest : ∀ b : Fin (x.regs one + 1),
        ExecWithin w (ram[addr ← baseReg + cnt; *addr ← val; cnt ← cnt + one])
          (x.set val b.val) (Y b.val) 3 := fun b =>
      WP.execWithin (c := ram[addr ← baseReg + cnt; *addr ← val; cnt ← cnt + one]) (by
        wram_exec [hb_v, hc_v, hv_a, hc_a, hone_a, hone_v, hbReg, hj, ho]; rfl)
    have hbody := ExecRandLaw.rand_seq (w := w) (f := fun y => bitsAt y.mem base n)
      (P := fun y => ∃ b ≤ 1, y = Y b) (y := fun b => Y b.val)
      (by rw [ho]; exact hw1) hrest
      (fun b => ⟨b.val, by have := b.isLt; omega, rfl⟩)
    have hlaw := ExecRandLaw.loop_iter
      (Q := fun y =>
        (∀ i < n, y.mem (base + i) ≤ 1) ∧
        (∀ a, ¬(base ≤ a ∧ a < base + n) → y.mem a = x.mem a) ∧
        ∀ i : Fin r, i ≠ cnt → i ≠ val → i ≠ addr → y.regs i = x.regs i)
      (κ := fun σ' =>
        (PMF.uniformOfFintype (Fin n → Bool)).map fun τ i =>
          if i.val < j + 1 then σ' i else τ i) hc hbody (fun y ⟨b, hb, hy⟩ => by
      subst hy
      have hYc : (Y b).regs cnt = j + 1 := by simp [Y, Data.set_regs]
      have hYreg : ∀ i : Fin r, i ≠ cnt → i ≠ val → i ≠ addr → (Y b).regs i = x.regs i :=
        fun i hic hiv hia => by
          simp [Y, Data.set_regs, Data.write_regs, Function.update_of_ne hic,
            Function.update_of_ne hiv, Function.update_of_ne hia]
      have h := sampleBitsLoop_law hnd hw1 hw_end d (Y b)
        ((hYreg one hone_c hone_v hone_a).trans ho)
        ((hYreg baseReg hb_c hb_v hb_a).trans hbReg)
        ((hYreg nReg hn_c hn_v hn_a).trans hn)
        (by rw [hYc]; omega)
        (fun i hi => by
          rw [hYc] at hi
          simp only [Y, Data.set_mem, Data.write_mem, Function.update_apply]
          split_ifs
          exacts [hb, hbits i (by omega)])
      rw [hYc] at h
      exact h.mono (fun z ⟨hzb, hzm, hzr⟩ =>
        ⟨hzb,
         fun a ha => (hzm a ha).trans (by
           have hne : a ≠ base + j := by omega
           simp [Y, Data.set_mem, Data.write_mem, Function.update_of_ne hne]),
         fun i hic hiv hia => (hzr i hic hiv hia).trans (hYreg i hic hiv hia)⟩) le_rfl le_rfl)
    refine (hlaw.congr_law ?_).mono (fun _ h => h) (by omega) (by omega)
    rw [ho, PMF.bind_map]
    have hYa (b : ℕ) : bitsAt (Y b).mem base n =
        Function.update (bitsAt x.mem base n) ⟨j, hjn⟩ (decide (b = 1)) :=
      bitsAt_update_self x.mem base ⟨j, hjn⟩ b
    let G : (Fin n → Bool) → (Fin n → Bool) := fun τ i =>
      if i.val < j then bitsAt x.mem base n i else τ i
    have hcomp (b : Bool) : (fun τ : Fin n → Bool => fun i : Fin n =>
        if i.val < j + 1 then Function.update (bitsAt x.mem base n) ⟨j, hjn⟩ b i else τ i) =
        G ∘ fun τ => Function.update τ ⟨j, hjn⟩ b := by
      funext τ i
      simp only [G, Function.comp_apply, Function.update_apply, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    calc (PMF.uniformOfFintype (Fin (1 + 1))).bind
          ((fun σ' => (PMF.uniformOfFintype (Fin n → Bool)).map fun τ i =>
            if i.val < j + 1 then σ' i else τ i) ∘ fun b => bitsAt (Y b.val).mem base n)
        = (PMF.uniformOfFintype (Fin (1 + 1))).bind (fun b =>
            ((PMF.uniformOfFintype (Fin n → Bool)).map
              fun τ => Function.update τ ⟨j, hjn⟩ (finTwoEquiv b)).map G) := by
          congr 1 with b : 1
          have hb : decide (b.val = 1) = finTwoEquiv b := by fin_cases b <;> rfl
          simp only [Function.comp_apply, hYa, hb, hcomp, PMF.map_comp]
      _ = ((PMF.uniformOfFintype Bool).bind fun b =>
            (PMF.uniformOfFintype (Fin n → Bool)).map
              fun τ => Function.update τ ⟨j, hjn⟩ b).map G := by
          rw [← PMF.uniformOfFintype_map_equiv finTwoEquiv, PMF.bind_map, PMF.map_bind]; rfl
      _ = _ := by rw [PMF.uniformOfFintype_update]

/-- **Uniform bit-slice sampling.** When `[one, baseReg, nReg, cnt, val, addr]` are distinct
registers with `regs zero = 0`, `regs one = 1`, `regs baseReg = base` and `regs nReg = n`,
`sampleBits` halts within `6 * n + 3` instructions and `n` `rand` calls, writes `0`/`1` words across
`[base, base + n)` whose `bitsAt` view is distributed uniformly on `Fin n → Bool`, leaves memory
outside `[base, base + n)` unchanged, and preserves all registers outside `{cnt, val, addr}`. -/
theorem sampleBits_law {w base n : ℕ}
    {zero one baseReg nReg cnt val addr : Fin r}
    (hdistinct : [one, baseReg, nReg, cnt, val, addr].Nodup)
    (hw1 : Fits w 1) (hw_end : Fits w (base + n))
    {x : Data r} (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hbReg : x.regs baseReg = base) (hn : x.regs nReg = n) :
    ExecRandLaw w (sampleBits zero one baseReg nReg cnt val addr) x
      (fun y =>
        (∀ i < n, y.mem (base + i) ≤ 1) ∧
        (∀ a, ¬(base ≤ a ∧ a < base + n) → y.mem a = x.mem a) ∧
        ∀ i : Fin r, i ≠ cnt → i ≠ val → i ≠ addr → y.regs i = x.regs i)
      (6 * n + 3) n
      (fun y => bitsAt y.mem base n)
      (PMF.uniformOfFintype (Fin n → Bool)) := by
  have hd' := hdistinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  have h := sampleBitsLoop_law hdistinct hw1 hw_end n (x.set cnt 0)
    (by simp [Data.set_regs, Function.update_of_ne hd'.1.2.2.1, ho])
    (by simp [Data.set_regs, Function.update_of_ne hd'.2.1.2.1, hbReg])
    (by simp [Data.set_regs, Function.update_of_ne hd'.2.2.1.1, hn])
    (by simp) (by simp)
  simp only [Data.set_regs, Function.update_self, Nat.not_lt_zero, ↓reduceIte] at h
  have hid : (fun τ : Fin n → Bool => fun i => τ i) = id := rfl
  rw [hid, PMF.map_id] at h
  have hcopy := hz ▸ ExecWithin.copy (B := .standard) (w := w) (d := cnt) (s := zero) (x := x)
  exact (ExecRandLaw.seq_det hcopy h).mono
    (fun y ⟨hyb, hym, hyr⟩ =>
      ⟨hyb, hym, fun i hic hiv hia =>
        (hyr i hic hiv hia).trans (by simp [Function.update_of_ne hic])⟩)
    (by omega) le_rfl

/-! ### Query-bound transfer for fixed-register `rand` calls -/

/-- Syntactic check that every `rand` instruction in `c` reads register `s`. -/
@[expose]
def Code.usesRandSrc (s : Fin r) : Code B r → Bool
  | .op _ => true
  | .rand _ src => src == s
  | .seq c₁ c₂ => c₁.usesRandSrc s && c₂.usesRandSrc s
  | .branch _ pos neg => pos.usesRandSrc s && neg.usesRandSrc s
  | .loop _ body => body.usesRandSrc s

@[simp]
theorem usesRandSrc_sampleBits {zero one baseReg nReg cnt val addr s : Fin r} :
    (sampleBits zero one baseReg nReg cnt val addr).usesRandSrc s = (one == s) := by
  simp [sampleBits, Code.usesRandSrc]

/-- When `c` preserves register `s` holding `u` and every `rand` in `c` reads `s`, every oracle
query issued along `ExecRand w c x m` equals `u`. -/
theorem ExecRand.queriesSatisfy_eq_of_usesRandSrc {w u : ℕ} {s : Fin r} {c : Code B r}
    {x : Data r} {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m)
    (hs : x.regs s = u) (hp : c.Preserves s) (hu : c.usesRandSrc s = true) :
    Cslib.OracleComp.QueriesSatisfy (· = u) m := by
  induction h with
  | @op _ x' y' _ => exact Cslib.OracleComp.QueriesSatisfy.pure _
  | @rand dst src x' _ =>
    simp only [Code.usesRandSrc, beq_iff_eq] at hu
    subst hu
    have hq : Cslib.OracleComp.QueriesSatisfy (· = u) (ProbComp.unifFin (x'.regs src)) :=
      Cslib.OracleComp.QueriesSatisfy.query (p := (· = u)) hs
    simpa only [Cslib.OracleComp.QueriesSatisfy, Nat.add_zero] using
      Cslib.OracleComp.IsCostBounded.bind_on_support hq
        fun _ _ => Cslib.OracleComp.QueriesSatisfy.pure _
  | @seq _ _ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [Code.usesRandSrc, Bool.and_eq_true] at hu
    simpa only [Cslib.OracleComp.QueriesSatisfy, Nat.add_zero] using
      Cslib.OracleComp.IsCostBounded.bind_on_support (ih₁ hs hp.1 hu.1) fun z hz =>
        Cslib.OracleComp.IsCostBounded.bind_on_support
          (ih₂ z hz ((h₁.regs_eq hp.1 hz).trans hs) hp.2 hu.2)
          fun _ _ => Cslib.OracleComp.QueriesSatisfy.pure _
  | branch_pos _ _ ih =>
    simp only [Code.usesRandSrc, Bool.and_eq_true] at hu
    exact (Cslib.OracleComp.isCostBounded_map_iff _ _ 0).mpr (ih hs hp.1 hu.1)
  | branch_neg _ _ ih =>
    simp only [Code.usesRandSrc, Bool.and_eq_true] at hu
    exact (Cslib.OracleComp.isCostBounded_map_iff _ _ 0).mpr (ih hs hp.2 hu.2)
  | loop_exit _ => exact Cslib.OracleComp.QueriesSatisfy.pure _
  | @loop_iter _ _ _ _ _ _ hb _ ihb ihl =>
    simpa only [Cslib.OracleComp.QueriesSatisfy, Nat.add_zero] using
      Cslib.OracleComp.IsCostBounded.bind_on_support (ihb hs hp hu) fun z hz =>
        Cslib.OracleComp.IsCostBounded.bind_on_support
          (ihl z hz ((hb.regs_eq hp hz).trans hs) hp hu)
          fun _ _ => Cslib.OracleComp.QueriesSatisfy.pure _

end Cslib.WordRAM
