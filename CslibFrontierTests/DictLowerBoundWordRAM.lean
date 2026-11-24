/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.LowerBound
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Word-RAM Dynamic Succinct Dictionary Lower-Bound Client and Non-Vacuity Tests

Kernel-checked concrete `Basis.standard` Word-RAM dictionary implementations, sequential execution
sanity checks, generic transfer bridge instantiations, and non-vacuity checks for all 6 primary
actual-expected-time headline theorems and 6 certified-budget corollaries of
`CslibFrontier.DataStructure.Dictionary.WordRAM.LowerBound` ([LiLiangYuZhou2023],
`arXiv:2306.02253v3`, Theorems 1.1–1.3 and Section 1 footnote 1):

1. **Concrete 2-slot `Basis.standard` Word-RAM dynamic dictionaries (`twoSlotDetImpl`,
   `twoSlotRandImpl`):**
   - Stores up to `n = 2` active `(key, value)` pairs of `Dynamic.spec U V 2` in two `w`-bit memory
     words `[base, base + 2)` (`0` = empty, `(u.1 + 1) * V + v` = occupied `(u, v)`) whenever
     `(U + 1) * V ≤ 2 ^ w` and `Fits w (base + 2)`.
   - Supports both **zero persistent registers** (`usePersBase = false`, `base = 0`,
     `persistentRegCount = 0`) and **positive persistent registers** (`usePersBase = true`,
     `base = 2` held in `r0`, `persistentRegCount = 1`), and provides a genuine coin-flipping
     (`Code.rand`) zero-error Las Vegas implementation `twoSlotRandImpl`.
   - Sequential execution sanity check (`twoSlot_trace_and_rand_sanity`) verifies an explicit
     `insert → insert → query → delete → insert → query → query` sequence end-to-end from fresh
     initialization and `not_execFlatProgramOps_halt_zero_time` confirms that `[Instr.halt retReg]`
     cannot satisfy `ExecFlatProgramOps` on `validHistoriesUpTo`.
2. **All 4 generic cell-probe-to-Word-RAM transfer bridges (`all_four_transfer_bridges_concrete`):**
   instantiates `expectedFlatTime_ge_of_indexedScheme`,
   `expectedFlatTime_update_ge_of_indexedScheme`, `expectedTotalCost_ge_of_indexedScheme` (at both
   `persistentRegCount = 0` and `persistentRegCount = 1` via `StateTransitionImpl.toRandomized`),
   and `expectedTotalCost_update_ge_of_indexedScheme` with `det_expectedSeqProbes_ge_linear`.
3. **Query-inclusive Word-RAM headlines & corollaries (Theorems 1.1 & 1.2 + combined):**
   instantiates `expectedFlatTime_ge_of_iterLog_redundancy` (including the `k = Nat.logStar 2`
   `O(n)`-redundancy specialization), `expectedFlatTime_ge_of_sublinear_redundancy`, and
   `expectedFlatTime_ge_iterLogStar_add_log_div` — plus their 3 `expectedTotalCost_*`
   certified-budget corollaries — on deterministic `twoSlotDetImpl.toRandomized` and coin-flipping
   `twoSlotRandImpl` at `(U = 31, V = 2, n = 2, k = 1, w = 6, R = 3 / 2)` with strictly positive
   lower bounds (`0 < log₂(4 / 3)`), plus relocated `persistentRegCount = 1` (`base = 2, r_max = 1`)
   instantiations.
4. **Update-only Word-RAM headlines & corollaries (Theorem 1.3(1)–(2) + combined):**
   instantiates `expectedFlatTime_update_ge_iterLog`, `expectedFlatTime_update_ge_sublinear`, and
   `expectedFlatTime_update_ge_iterLogStar_add_log_div` — plus their 3 `expectedTotalCost_update_*`
   certified-budget corollaries — on `twoSlotDetImpl.toRandomized` and `twoSlotRandImpl` at
   `(U = 15, V = 1024, n = 2, k = 1, w = 14, R = 3 / 2, α_V = 1)` with strictly positive bounds.
-/

public section

namespace CslibFrontierTests.DictLowerBoundWordRAM

open Cslib Cslib.WordRAM Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.CellProbe Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.CellProbe Cslib.DataStructure.Dictionary.WordRAM
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ### 1. Concrete 2-Slot `Basis.standard` Word-RAM Dynamic Dictionary (Det & `Code.rand`) -/

/-- Word encoding of a single slot: `0` for empty, `(u.1 + 1) * V + v.1` for occupied `(u, v)`. -/
def encodeSlot {U V : ℕ} : Option (Fin U × Fin V) → ℕ
  | none => 0
  | some (u, v) => (u.1 + 1) * V + v.1

/-- Key tag of a slot (`0` for empty, `u.1 + 1` for key `u`). -/
def slotKeyTag {U V : ℕ} : Option (Fin U × Fin V) → ℕ
  | none => 0
  | some (u, _) => u.1 + 1

private theorem encodeSlot_fits {U V w : ℕ} (hfit : (U + 1) * V ≤ 2 ^ w)
    (e : Option (Fin U × Fin V)) : Fits w (encodeSlot e) := by
  cases e with
  | none => exact fits_zero w
  | some uv =>
    rcases uv with ⟨u, v⟩
    dsimp only [encodeSlot, Fits]
    have hu := u.2
    have hv := v.2
    calc (u.1 + 1) * V + v.1
      _ < (u.1 + 1) * V + V := by omega
      _ = (u.1 + 2) * V := by ring
      _ ≤ (U + 1) * V := Nat.mul_le_mul_right V (by omega)
      _ ≤ 2 ^ w := hfit

private theorem encodeSlot_div {U V : ℕ} (hV : 1 ≤ V) (e : Option (Fin U × Fin V)) :
    encodeSlot e / V = slotKeyTag e := by
  cases e with
  | none => simp [encodeSlot, slotKeyTag]
  | some uv =>
    rcases uv with ⟨u, v⟩
    dsimp only [encodeSlot, slotKeyTag]
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt v.2, add_zero]

private theorem encodeSlot_mod {U V : ℕ} (u : Fin U) (v : Fin V) :
    encodeSlot (some (u, v)) % V = v.1 := by
  dsimp only [encodeSlot]
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt v.2]

/-- Abstract dictionary state induced by two disjoint-key slots `e0, e1`. -/
def slotsState {U V : ℕ} (e0 e1 : Option (Fin U × Fin V)) (u : Fin U) : Option ℕ :=
  match e0 with
  | some (u0, v0) =>
      if u = u0 then some v0.1
      else match e1 with
        | some (u1, v1) => if u = u1 then some v1.1 else none
        | none => none
  | none =>
      match e1 with
      | some (u1, v1) => if u = u1 then some v1.1 else none
      | none => none

private theorem two_le_card_dom_slotsState {U V : ℕ} {u0 u1 : Fin U} (v0 v1 : Fin V)
    (hne : u0 ≠ u1) :
    2 ≤ (Dictionary.dom (slotsState (some (u0, v0)) (some (u1, v1)))).card := by
  have hsub : ({u0, u1} : Finset (Fin U)) ⊆
      Dictionary.dom (slotsState (some (u0, v0)) (some (u1, v1))) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [Dictionary.dom, slotsState]
    · simp [Dictionary.dom, slotsState, hne.symm]
  have hcard : ({u0, u1} : Finset (Fin U)).card = 2 := Finset.card_pair hne
  exact hcard ▸ Finset.card_le_card hsub

/-- `query` branch of the 2-slot Word-RAM dictionary (`r0 = base`, `r2 = u.1 + 1`, `r3 = 0`,
`r4 = 1`, `r5 = V`, `r7 = base + 1`, result in `r8`: `0` if absent, `v + 1` if present). -/
def twoSlotQueryCode : Code .standard 9 :=
  .seq (.seq (.op (.load 8 0)) (.op (.bin .div 6 8 5)))
    (.branch (.eq 6 2)
      (.seq (.op (.bin .mod 8 8 5)) (.op (.bin .add 8 8 4)))
      (.seq (.seq (.op (.load 8 7)) (.op (.bin .div 6 8 5)))
        (.branch (.eq 6 2)
          (.seq (.op (.bin .mod 8 8 5)) (.op (.bin .add 8 8 4)))
          (.op (.copy 8 3)))))

/-- `insert` branch (`r0 = base`, `r2 = u.1 + 1`, `r3 = 0`, `r5 = V`,
`r6 = (u.1 + 1) * V + v`, `r7 = base + 1`, `r8 = mem[base] / V`). -/
def twoSlotInsertCode : Code .standard 9 :=
  .branch (.eq 8 2)
    (.op (.store 0 6))
    (.seq (.seq (.op (.load 1 7)) (.op (.bin .div 1 1 5)))
      (.branch (.eq 1 2)
        (.op (.store 7 6))
        (.branch (.eq 8 3)
          (.op (.store 0 6))
          (.op (.store 7 6)))))

/-- `delete` branch (`r0 = base`, `r2 = u.1 + 1`, `r3 = 0`, `r5 = V`, `r7 = base + 1`,
`r8 = mem[base] / V`). -/
def twoSlotDeleteCode : Code .standard 9 :=
  .branch (.eq 8 2)
    (.op (.store 0 3))
    (.seq (.seq (.op (.load 1 7)) (.op (.bin .div 1 1 5)))
      (.branch (.eq 1 2)
        (.op (.store 7 3))
        (.op (.copy 8 3))))

/-- Complete deterministic 2-slot operation body (`≤ 16` steps on every path). -/
def twoSlotBodyCode : Code .standard 9 :=
  .seq (.op (.bin .add 7 0 4))
    (.branch (.eq 1 3)
      twoSlotQueryCode
      (.seq (.seq (.op (.load 8 0)) (.op (.bin .div 8 8 5)))
        (.branch (.eq 1 4) twoSlotInsertCode twoSlotDeleteCode)))

/-- Deterministic 2-slot `SubroutineCode`: `usePersBase = false` marks all 9 registers caller-input
(`persistentRegCount = 0`); `usePersBase = true` keeps `r0 = base` persistent
(`persistentRegCount = 1`). -/
def twoSlotDetCode (base : ℕ) (usePersBase : Bool) : SubroutineCode .standard 9 0 where
  allocSpan := .seq (.op (.copy 0 1)) (.op (.const 1 (base + 2)))
  initSetup := .op (.const 3 0)
  code := twoSlotBodyCode
  frontierReg := 1
  baseReg := 0
  initParams := Fin.elim0
  curReg := 2
  zeroReg := 3
  oneReg := 4
  incCur := .bin .add 2 2 4
  input i := if usePersBase then decide (1 ≤ i.val) else true
  output := 8

/-- Coin-flipping (`Code.rand`) 2-slot `SubroutineCode` (`¬Code.IsRandFree`): samples a uniform
bit into `r8` via `Code.rand 8 4` before running `twoSlotBodyCode`. -/
def twoSlotRandCode (base : ℕ) (usePersBase : Bool) : SubroutineCode .standard 9 0 :=
  { twoSlotDetCode base usePersBase with
    code := .seq (.rand 8 4) twoSlotBodyCode }

theorem persistentRegCount_twoSlot_false (base : ℕ) :
    persistentRegCount (twoSlotDetCode base false) = 0 ∧
      persistentRegCount (twoSlotRandCode base false) = 0 :=
  ⟨persistentRegCount_eq_zero_of_all_input fun _ => rfl,
   persistentRegCount_eq_zero_of_all_input fun _ => rfl⟩

theorem persistentRegCount_twoSlot_true (base : ℕ) :
    persistentRegCount (twoSlotDetCode base true) = 1 ∧
      persistentRegCount (twoSlotRandCode base true) = 1 :=
  ⟨by change (Finset.univ.filter fun i : Fin 9 => !decide (1 ≤ i.val)).card = 1; decide,
   by change (Finset.univ.filter fun i : Fin 9 => !decide (1 ≤ i.val)).card = 1; decide⟩

/-- Caller register encoding for `Dynamic.Op U`. -/
def twoSlotEncode (U V base : ℕ) (o : Dynamic.Op U) (i : Fin 9) : ℕ :=
  if i.val = 0 then base
  else if i.val = 1 then
    match o with | .query _ => 0 | .insert _ _ => 1 | .delete _ => 2
  else if i.val = 2 then
    match o with | .query u | .insert u _ | .delete u => u.1 + 1
  else if i.val = 4 then 1
  else if i.val = 5 then V
  else if i.val = 6 then
    match o with | .insert u v => if v < V then (u.1 + 1) * V + v else 0 | _ => 0
  else 0

/-- Register-agreement predicate matching `r1`..`r6` against `twoSlotEncode`. -/
def twoSlotArgMatch (U V base : ℕ) (o : Dynamic.Op U) (regs : Fin 9 → ℕ) : Prop :=
  ∀ i : Fin 9, 1 ≤ i.val ∧ i.val ≤ 6 → regs i = twoSlotEncode U V base o i

/-- Decode the Word-RAM return register `r8` to the dictionary operation result. -/
def twoSlotDecode {U : ℕ} : (o : Dynamic.Op U) → (Fin 9 → ℕ) → Option o.Result
  | .query _, regs => some (if regs 8 == 0 then none else some (regs 8 - 1))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

/-- Representation invariant for the 2-slot Word-RAM dictionary at `[base, base + 2)`. -/
def TwoSlotRep (U V w base : ℕ) (usePersBase : Bool) (s : Dictionary.State U) (x : Data 9) : Prop :=
  x.Bounded w ∧
    (usePersBase = true → x.regs 0 = base) ∧
    ∃ e0 e1 : Option (Fin U × Fin V),
      (∀ u0 v0 u1 v1, e0 = some (u0, v0) → e1 = some (u1, v1) → u0 ≠ u1) ∧
      x.mem base = encodeSlot e0 ∧
      x.mem (base + 1) = encodeSlot e1 ∧
      s = slotsState e0 e1

private theorem fits_from_params {U V w base : ℕ} (hU : 1 ≤ U) (hw : 2 ≤ w)
    (hUV : (U + 1) * V ≤ 2 ^ w) (hbase : Fits w (base + 2)) :
    Fits w 1 ∧ Fits w 2 ∧ Fits w V ∧ Fits w base ∧ Fits w (base + 1) ∧ Fits w (base + 2) := by
  have hpow : 4 ≤ 2 ^ w :=
    Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) hw)
  have hV_lt : V < 2 ^ w := by
    have : 2 * V ≤ 2 ^ w :=
      (Nat.mul_le_mul_right V (show 2 ≤ U + 1 by omega)).trans hUV
    omega
  have hbm : base + 2 < 2 ^ w := hbase
  exact ⟨by dsimp [Fits]; omega, by dsimp [Fits]; omega, hV_lt,
    by dsimp [Fits]; omega, by dsimp [Fits]; omega, hbase⟩

private theorem twoSlot_arguments_fit {U V w base : ℕ} (usePersBase : Bool)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hw : 2 ≤ w) (hUV : (U + 1) * V ≤ 2 ^ w)
    (hbase : Fits w (base + 2)) :
    ∀ {s : Dictionary.State U} (o : Dynamic.Op U), (Dynamic.spec U V 2).valid s o →
      ∀ i : Fin 9, (twoSlotDetCode base usePersBase).input i = true →
        Fits w (twoSlotEncode U V base o i) := by
  obtain ⟨hf1, hf2, hfV, hfb, _, _⟩ := fits_from_params hU hw hUV hbase
  intro _ o _ i _
  have hu_fit : ∀ u : Fin U, Fits w (u.1 + 1) := fun u => by
    have hu := u.2
    have : u.1 + 1 < (U + 1) * V := by
      calc u.1 + 1 ≤ U * 1 := by omega
        _ ≤ U * V := Nat.mul_le_mul_left U hV
        _ < U * V + V := Nat.lt_add_of_pos_right (by omega)
        _ = (U + 1) * V := (Nat.add_one_mul U V).symm
    exact lt_of_lt_of_le this hUV
  fin_cases i <;> simp only [twoSlotEncode, ↓reduceIte]
  · exact hfb
  · cases o <;> simp [fits_zero, hf1, hf2]
  · cases o with
    | query u | insert u _ | delete u => exact hu_fit u
  · exact fits_zero w
  · exact hf1
  · exact hfV
  · cases o with
    | query _ => exact fits_zero w
    | delete _ => exact fits_zero w
    | insert u v =>
      by_cases hv : v < V
      · simpa [hv, encodeSlot] using encodeSlot_fits hUV (some (u, ⟨v, hv⟩))
      · simp [hv, fits_zero]
  · exact fits_zero w
  · exact fits_zero w

private theorem exec_loadDiv {U V w : ℕ} (hV : 1 ≤ V) (hUV : (U + 1) * V ≤ 2 ^ w)
    (d : Data 9) (hd : d.Bounded w) (valReg dstReg addrReg : Fin 9) (h5 : valReg ≠ 5)
    (hV_reg : d.regs 5 = V) (e : Option (Fin U × Fin V))
    (hmem : d.mem (d.regs addrReg) = encodeSlot e) :
    let d₁ := d.set valReg (d.mem (d.regs addrReg))
    let d₂ := d₁.set dstReg (BinOp.div.eval (d₁.regs valReg) (d₁.regs 5))
    ExecWithin w (.seq (.op (.load valReg addrReg)) (.op (.bin .div dstReg valReg 5))) d d₂ 2 ∧
      d₂.Bounded w ∧
      d₂.regs dstReg = slotKeyTag e := by
  have hfit_div : Fits w (BinOp.div.eval ((d.set valReg (d.mem (d.regs addrReg))).regs valReg)
      ((d.set valReg (d.mem (d.regs addrReg))).regs 5)) := by
    simp only [Data.set, Function.update_self, Function.update_of_ne h5.symm, hmem, hV_reg,
      BinOp.eval]
    exact lt_of_le_of_lt (Nat.div_le_self _ V) (encodeSlot_fits hUV e)
  refine ⟨ExecWithin.load.seq (ExecWithin.bin hfit_div),
    (hd.set (hd.2 _)).set hfit_div, ?_⟩
  simp only [Data.set, Function.update_self, Function.update_of_ne h5.symm, hmem, hV_reg,
    BinOp.eval, encodeSlot_div hV]

private theorem exec_queryExtract {U V w : ℕ} (hU : 1 ≤ U) (hUV : (U + 1) * V ≤ 2 ^ w)
    (d : Data 9) (hd : d.Bounded w) (u : Fin U) (v : Fin V)
    (hr8 : d.regs 8 = encodeSlot (some (u, v))) (hr4 : d.regs 4 = 1) (hr5 : d.regs 5 = V) :
    let d₁ := d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))
    let d₂ := d₁.set 8 (BinOp.add.eval (d₁.regs 8) (d₁.regs 4))
    ExecWithin w (.seq (.op (.bin .mod 8 8 5)) (.op (.bin .add 8 8 4))) d d₂ 2 ∧
      d₂.Bounded w ∧ d₂.regs 8 = v.1 + 1 := by
  have hmod_eq : BinOp.mod.eval (d.regs 8) (d.regs 5) = v.1 := by
    simp [BinOp.eval, hr8, hr5, encodeSlot_mod]
  have h2V : 2 * V ≤ 2 ^ w := (Nat.mul_le_mul_right V (by omega)).trans hUV
  have hmod_fit : Fits w (BinOp.mod.eval (d.regs 8) (d.regs 5)) := by
    rw [hmod_eq]; dsimp [Fits]; have := v.2; omega
  have hadd_eq : BinOp.add.eval ((d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))).regs 8)
      ((d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))).regs 4) = v.1 + 1 := by
    have h1 : (d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))).regs 8 = v.1 := by
      simp [Data.set, hr8, hr5, encodeSlot_mod]
    have h2 : (d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))).regs 4 = 1 := by
      simp [Data.set, hr4]
    change _ + _ = _
    rw [h1, h2]
  have hadd_fit : Fits w (BinOp.add.eval ((d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))).regs 8)
      ((d.set 8 (BinOp.mod.eval (d.regs 8) (d.regs 5))).regs 4)) := by
    rw [hadd_eq]; dsimp [Fits]; have := v.2; omega
  exact ⟨(ExecWithin.bin hmod_fit).seq (ExecWithin.bin hadd_fit),
    (hd.set hmod_fit).set hadd_fit, by simpa [Data.set] using hadd_eq⟩

private theorem slotsState_none_of_ne_tags {U V : ℕ} {e0 e1 : Option (Fin U × Fin V)} {u : Fin U}
    (hk0 : slotKeyTag e0 ≠ u.1 + 1) (hk1 : slotKeyTag e1 ≠ u.1 + 1) :
    slotsState e0 e1 u = none := by
  cases e0 with
  | none =>
    cases e1 with
    | none => rfl
    | some uv1 =>
      have hne1 : u ≠ uv1.1 := fun h => hk1 (by simp [h, slotKeyTag])
      simp [slotsState, hne1]
  | some uv0 =>
    have hne0 : u ≠ uv0.1 := fun h => hk0 (by simp [h, slotKeyTag])
    cases e1 with
    | none => simp [slotsState, hne0]
    | some uv1 =>
      have hne1 : u ≠ uv1.1 := fun h => hk1 (by simp [h, slotKeyTag])
      simp [slotsState, hne0, hne1]

private theorem twoSlotBody_exec {U V w base : ℕ} (usePersBase : Bool)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hw : 2 ≤ w) (hUV : (U + 1) * V ≤ 2 ^ w)
    (hbase : Fits w (base + 2))
    {s : Dictionary.State U} {x : Data 9} (o : Dynamic.Op U)
    (hrep : TwoSlotRep U V w base usePersBase s x)
    (hval : (Dynamic.spec U V 2).valid s o)
    (hr0 : x.regs 0 = base)
    (hmatch : twoSlotArgMatch U V base o x.regs) :
    ∃ y, ExecWithin w twoSlotBodyCode x y 16 ∧
      twoSlotDecode o y.regs = some ((Dynamic.spec U V 2).stepFn s o).2 ∧
      TwoSlotRep U V w base usePersBase ((Dynamic.spec U V 2).stepFn s o).1 y ∧
      Modifies (Block.mk base 2).footprint x.mem y.mem := by
  obtain ⟨_, _, _, _, hfb1, _⟩ := fits_from_params hU hw hUV hbase
  rcases hrep with ⟨hbdd, _, e0, e1, hdisj, hm0, hm1, hs_eq⟩
  have hr3 : x.regs 3 = 0 := by simpa [twoSlotEncode] using hmatch 3 (by decide)
  have hr4 : x.regs 4 = 1 := by simpa [twoSlotEncode] using hmatch 4 (by decide)
  have hr5 : x.regs 5 = V := by simpa [twoSlotEncode] using hmatch 5 (by decide)
  have hadd7_fit : Fits w (BinOp.add.eval (x.regs 0) (x.regs 4)) := by
    simpa [BinOp.eval, hr0, hr4] using hfb1
  let x₁ := x.set 7 (BinOp.add.eval (x.regs 0) (x.regs 4))
  have hx₁_bdd : x₁.Bounded w := hbdd.set hadd7_fit
  have hs1 : ExecWithin w (.op (.bin .add 7 0 4)) x x₁ 1 := ExecWithin.bin hadd7_fit
  have hfp0 : base ∈ (Block.mk base 2).footprint := by simp [Block.mem_footprint, Block.Owns]
  have hfp1 : base + 1 ∈ (Block.mk base 2).footprint := by simp [Block.mem_footprint, Block.Owns]
  have hmod_write0 : ∀ val,
      Modifies (Block.mk base 2).footprint x.mem (Function.update x.mem base val) :=
    fun val a ha => Function.update_of_ne (by rintro rfl; exact ha hfp0) val x.mem
  have hmod_write1 : ∀ val,
      Modifies (Block.mk base 2).footprint x.mem (Function.update x.mem (base + 1) val) :=
    fun val a ha => Function.update_of_ne (by rintro rfl; exact ha hfp1) val x.mem
  have hwrite_bdd : ∀ {z : Data 9}, z.Bounded w → ∀ addr val, Fits w val →
      (z.write addr val).Bounded w := fun hz addr val hfv =>
    ⟨hz.1, fun a => by by_cases ha : a = addr <;> simp [Data.write, ha, hfv, hz.2 a]⟩
  -- Shared update slot-0 and slot-1 `load`+`div` prefixes reused by both `insert` and `delete`.
  let xu₂ := x₁.set 8 (x₁.mem (x₁.regs 0))
  let xu₃ := xu₂.set 8 (BinOp.div.eval (xu₂.regs 8) (xu₂.regs 5))
  obtain ⟨he_pre, hxu₃_bdd, hxu₃_tag0⟩ :=
    exec_loadDiv hV hUV x₁ hx₁_bdd 8 8 0 (by decide) (by simpa [x₁] using hr5) e0
      (by simpa [x₁, hr0] using hm0)
  let xu₄ := xu₃.set 1 (xu₃.mem (xu₃.regs 7))
  let xu₅ := xu₄.set 1 (BinOp.div.eval (xu₄.regs 1) (xu₄.regs 5))
  obtain ⟨he_l1, hxu₅_bdd, hxu₅_tag1⟩ :=
    exec_loadDiv hV hUV xu₃ hxu₃_bdd 1 1 7 (by decide) (by simpa [xu₃, xu₂, x₁] using hr5) e1
      (by simpa [xu₃, xu₂, x₁, BinOp.eval, hr0, hr4] using hm1)
  cases o with
  | query u =>
    have hr1 : x.regs 1 = 0 := by simpa [twoSlotEncode] using hmatch 1 (by decide)
    have hr2 : x.regs 2 = u.1 + 1 := by simpa [twoSlotEncode] using hmatch 2 (by decide)
    have hc_op : (Cond.eq (1 : Fin 9) 3).Holds x₁ := by simp [x₁, hr1, hr3]
    let x₂ := x₁.set 8 (x₁.mem (x₁.regs 0))
    let x₃ := x₂.set 6 (BinOp.div.eval (x₂.regs 8) (x₂.regs 5))
    obtain ⟨he_load0, hx₃_bdd, hx₃_tag0⟩ :=
      exec_loadDiv hV hUV x₁ hx₁_bdd 8 6 0 (by decide) (by simpa [x₁] using hr5) e0
        (by simpa [x₁, hr0] using hm0)
    by_cases hk0 : slotKeyTag e0 = u.1 + 1
    · cases e0 with
      | none => simp [slotKeyTag] at hk0
      | some uv0 =>
        rcases uv0 with ⟨u0, v0⟩
        have hu_eq : u = u0 := Fin.ext (by simpa [slotKeyTag] using hk0.symm)
        subst hu_eq
        have hc0 : (Cond.eq (6 : Fin 9) 2).Holds x₃ := by
          change x₃.regs 6 = x₃.regs 2
          rw [hx₃_tag0]; simp [x₃, x₂, x₁, hr2, slotKeyTag]
        let x₄ := x₃.set 8 (BinOp.mod.eval (x₃.regs 8) (x₃.regs 5))
        let x₅ := x₄.set 8 (BinOp.add.eval (x₄.regs 8) (x₄.regs 4))
        obtain ⟨he_ext, hx₅_bdd, hx₅_r8⟩ := exec_queryExtract hU hUV x₃ hx₃_bdd u v0
          (by simpa [x₃, x₂, x₁, hr0] using hm0) (by simpa [x₃, x₂, x₁] using hr4)
          (by simpa [x₃, x₂, x₁] using hr5)
        have he_q : ExecWithin w twoSlotQueryCode x₁ x₅ 5 :=
          (he_load0.seq (ExecWithin.branch_pos hc0 he_ext)).mono (by omega)
        refine ⟨x₅, (hs1.seq (ExecWithin.branch_pos hc_op he_q)).mono (by omega), ?_, ?_,
          Modifies.refl _ _⟩
        · change some (if x₅.regs 8 == 0 then none else some (x₅.regs 8 - 1)) = _
          rw [show x₅.regs 8 = v0.1 + 1 from hx₅_r8]
          simp [hs_eq, slotsState, Dynamic.spec]
        · exact ⟨hx₅_bdd, fun _ => by simpa [x₅, x₄, x₃, x₂, x₁] using hr0,
            some (u, v0), e1, hdisj, hm0, hm1, hs_eq⟩
    · have hc0 : ¬(Cond.eq (6 : Fin 9) 2).Holds x₃ := by
        change x₃.regs 6 ≠ x₃.regs 2
        rw [hx₃_tag0]; simpa [x₃, x₂, x₁, hr2] using hk0
      let x₄ := x₃.set 8 (x₃.mem (x₃.regs 7))
      let x₅ := x₄.set 6 (BinOp.div.eval (x₄.regs 8) (x₄.regs 5))
      obtain ⟨he_load1, hx₅_bdd, hx₅_tag1⟩ :=
        exec_loadDiv hV hUV x₃ hx₃_bdd 8 6 7 (by decide) (by simpa [x₃, x₂, x₁] using hr5) e1
          (by simpa [x₃, x₂, x₁, BinOp.eval, hr0, hr4] using hm1)
      have hs_not0 : ∀ u0 v0, e0 = some (u0, v0) → u ≠ u0 := by
        rintro u0 v0 rfl h_eq; subst h_eq; exact hk0 rfl
      by_cases hk1 : slotKeyTag e1 = u.1 + 1
      · cases e1 with
        | none => simp [slotKeyTag] at hk1
        | some uv1 =>
          rcases uv1 with ⟨u1, v1⟩
          have hu_eq : u = u1 := Fin.ext (by simpa [slotKeyTag] using hk1.symm)
          subst hu_eq
          have hc1 : (Cond.eq (6 : Fin 9) 2).Holds x₅ := by
            change x₅.regs 6 = x₅.regs 2
            rw [hx₅_tag1]; simp [x₅, x₄, x₃, x₂, x₁, hr2, slotKeyTag]
          let x₆ := x₅.set 8 (BinOp.mod.eval (x₅.regs 8) (x₅.regs 5))
          let x₇ := x₆.set 8 (BinOp.add.eval (x₆.regs 8) (x₆.regs 4))
          obtain ⟨he_ext, hx₇_bdd, hx₇_r8⟩ := exec_queryExtract hU hUV x₅ hx₅_bdd u v1
            (by simpa [x₅, x₄, x₃, x₂, x₁, BinOp.eval, hr0, hr4] using hm1)
            (by simpa [x₅, x₄, x₃, x₂, x₁] using hr4)
            (by simpa [x₅, x₄, x₃, x₂, x₁] using hr5)
          have he_q : ExecWithin w twoSlotQueryCode x₁ x₇ 9 :=
            (he_load0.seq (ExecWithin.branch_neg hc0
              (he_load1.seq (ExecWithin.branch_pos hc1 he_ext)))).mono (by omega)
          refine ⟨x₇, (hs1.seq (ExecWithin.branch_pos hc_op he_q)).mono (by omega), ?_, ?_,
            Modifies.refl _ _⟩
          · change some (if x₇.regs 8 == 0 then none else some (x₇.regs 8 - 1)) = _
            rw [show x₇.regs 8 = v1.1 + 1 from hx₇_r8]
            cases e0 with
            | none => simp [hs_eq, slotsState, Dynamic.spec]
            | some uv0 =>
              simp [hs_eq, slotsState, hs_not0 uv0.1 uv0.2 rfl, Dynamic.spec]
          · exact ⟨hx₇_bdd, fun _ => by simpa [x₇, x₆, x₅, x₄, x₃, x₂, x₁] using hr0,
              e0, some (u, v1), hdisj, hm0, hm1, hs_eq⟩
      · have hc1 : ¬(Cond.eq (6 : Fin 9) 2).Holds x₅ := by
          change x₅.regs 6 ≠ x₅.regs 2
          rw [hx₅_tag1]; simpa [x₅, x₄, x₃, x₂, x₁, hr2] using hk1
        let x₆ := x₅.set 8 (x₅.regs 3)
        have he_q : ExecWithin w twoSlotQueryCode x₁ x₆ 9 :=
          (he_load0.seq (ExecWithin.branch_neg hc0
            (he_load1.seq (ExecWithin.branch_neg hc1 ExecWithin.copy)))).mono (by omega)
        refine ⟨x₆, (hs1.seq (ExecWithin.branch_pos hc_op he_q)).mono (by omega), ?_, ?_,
          Modifies.refl _ _⟩
        · have hs_u : s u = none := hs_eq ▸ slotsState_none_of_ne_tags hk0 hk1
          simp [twoSlotDecode, x₆, x₅, x₄, x₃, x₂, x₁, hr3, hs_u, Dynamic.spec]
        · exact ⟨hx₅_bdd.set (hx₅_bdd.1 3),
            fun _ => by simpa [x₆, x₅, x₄, x₃, x₂, x₁] using hr0,
            e0, e1, hdisj, hm0, hm1, hs_eq⟩
  | insert u v =>
    have hv_lt : v < V := hval.2
    let v_fin : Fin V := ⟨v, hv_lt⟩
    have hr1 : x.regs 1 = 1 := by simpa [twoSlotEncode] using hmatch 1 (by decide)
    have hr2 : x.regs 2 = u.1 + 1 := by simpa [twoSlotEncode] using hmatch 2 (by decide)
    have hr6 : x.regs 6 = encodeSlot (some (u, v_fin)) := by
      simpa [twoSlotEncode, hv_lt, encodeSlot, v_fin] using hmatch 6 (by decide)
    have hc_not_q : ¬(Cond.eq (1 : Fin 9) 3).Holds x₁ := by simp [x₁, hr1, hr3]
    have hc_ins : (Cond.eq (1 : Fin 9) 4).Holds xu₃ := by simp [xu₃, xu₂, x₁, hr1, hr4]
    by_cases hk0 : slotKeyTag e0 = u.1 + 1
    · cases e0 with
      | none => simp [slotKeyTag] at hk0
      | some uv0 =>
        rcases uv0 with ⟨u0, v0⟩
        have hu_eq : u = u0 := Fin.ext (by simpa [slotKeyTag] using hk0.symm)
        subst hu_eq
        have hc0 : (Cond.eq (8 : Fin 9) 2).Holds xu₃ := by
          change xu₃.regs 8 = xu₃.regs 2
          rw [hxu₃_tag0]; simp [xu₃, xu₂, x₁, hr2, slotKeyTag]
        let y := xu₃.write (xu₃.regs 0) (xu₃.regs 6)
        have he_ins : ExecWithin w twoSlotInsertCode xu₃ y 2 :=
          ExecWithin.branch_pos hc0 ExecWithin.store
        refine ⟨y,
          (hs1.seq (ExecWithin.branch_neg hc_not_q
            (he_pre.seq (ExecWithin.branch_pos hc_ins he_ins)))).mono (by omega),
          rfl, ?_, ?_⟩
        · refine ⟨hwrite_bdd hxu₃_bdd _ _ (hxu₃_bdd.1 6), fun _ => hr0, some (u, v_fin), e1,
            fun _ _ u1 v1 h0 h1 => ?_, ?_, ?_, ?_⟩
          · cases h0; exact hdisj u v0 u1 v1 rfl h1
          · simp [y, xu₃, xu₂, x₁, hr0, hr6]
          · simp [y, xu₃, xu₂, x₁, hr0, hm1]
          · ext u'
            rcases eq_or_ne u' u with rfl | hu'
            · simp [slotsState, v_fin]
            · simp [hs_eq, slotsState, hu']
        · simpa [y, xu₃, xu₂, x₁, hr0] using hmod_write0 (xu₃.regs 6)
    · have hc0 : ¬(Cond.eq (8 : Fin 9) 2).Holds xu₃ := by
        change xu₃.regs 8 ≠ xu₃.regs 2
        rw [hxu₃_tag0]; simpa [xu₃, xu₂, x₁, hr2] using hk0
      have hs_not0 : ∀ u0 v0, e0 = some (u0, v0) → u ≠ u0 := by
        rintro u0 v0 rfl h_eq; subst h_eq; exact hk0 rfl
      by_cases hk1 : slotKeyTag e1 = u.1 + 1
      · cases e1 with
        | none => simp [slotKeyTag] at hk1
        | some uv1 =>
          rcases uv1 with ⟨u1, v1⟩
          have hu_eq : u = u1 := Fin.ext (by simpa [slotKeyTag] using hk1.symm)
          subst hu_eq
          have hc1 : (Cond.eq (1 : Fin 9) 2).Holds xu₅ := by
            change xu₅.regs 1 = xu₅.regs 2
            rw [hxu₅_tag1]; simp [xu₅, xu₄, xu₃, xu₂, x₁, hr2, slotKeyTag]
          let y := xu₅.write (xu₅.regs 7) (xu₅.regs 6)
          have he_ins : ExecWithin w twoSlotInsertCode xu₃ y 6 :=
            (ExecWithin.branch_neg hc0
              (he_l1.seq (ExecWithin.branch_pos hc1 ExecWithin.store))).mono (by omega)
          refine ⟨y,
            (hs1.seq (ExecWithin.branch_neg hc_not_q
              (he_pre.seq (ExecWithin.branch_pos hc_ins he_ins)))).mono (by omega),
            rfl, ?_, ?_⟩
          · refine ⟨hwrite_bdd hxu₅_bdd _ _ (hxu₅_bdd.1 6), fun _ => hr0, e0, some (u, v_fin),
              fun u0 v0 _ _ h0 h1 => ?_, ?_, ?_, ?_⟩
            · cases h1; exact (hs_not0 u0 v0 h0).symm
            · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4, hm0]
            · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4, hr6]
            · ext u'
              cases e0 with
              | none =>
                rcases eq_or_ne u' u with rfl | hu'
                · simp [slotsState, v_fin]
                · simp [hs_eq, slotsState, hu']
              | some uv0 =>
                rcases uv0 with ⟨u0, v0⟩
                have hne0 := hs_not0 u0 v0 rfl
                rcases eq_or_ne u' u with rfl | hu'
                · simp [slotsState, hne0, v_fin]
                · simp [hs_eq, slotsState, hu']
          · simpa [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4] using hmod_write1 (xu₅.regs 6)
      · have hc1 : ¬(Cond.eq (1 : Fin 9) 2).Holds xu₅ := by
          change xu₅.regs 1 ≠ xu₅.regs 2
          rw [hxu₅_tag1]; simpa [xu₅, xu₄, xu₃, xu₂, x₁, hr2] using hk1
        have hs_not1 : ∀ u1 v1, e1 = some (u1, v1) → u ≠ u1 := by
          rintro u1 v1 rfl h_eq; subst h_eq; exact hk1 rfl
        cases e0 with
        | none =>
          have hc_z0 : (Cond.eq (8 : Fin 9) 3).Holds xu₅ := by
            change xu₅.regs 8 = xu₅.regs 3
            have hr8_eq : xu₅.regs 8 = xu₃.regs 8 := by simp [xu₅, xu₄]
            rw [hr8_eq, show xu₃.regs 8 = slotKeyTag (none : Option (Fin U × Fin V)) from hxu₃_tag0]
            simp [xu₅, xu₄, xu₃, xu₂, x₁, hr3, slotKeyTag]
          let y := xu₅.write (xu₅.regs 0) (xu₅.regs 6)
          have he_ins : ExecWithin w twoSlotInsertCode xu₃ y 8 :=
            (ExecWithin.branch_neg hc0 (he_l1.seq (ExecWithin.branch_neg hc1
              (ExecWithin.branch_pos hc_z0 ExecWithin.store)))).mono (by omega)
          refine ⟨y,
            (hs1.seq (ExecWithin.branch_neg hc_not_q
              (he_pre.seq (ExecWithin.branch_pos hc_ins he_ins)))).mono (by omega),
            rfl, ?_, ?_⟩
          · refine ⟨hwrite_bdd hxu₅_bdd _ _ (hxu₅_bdd.1 6), fun _ => hr0, some (u, v_fin), e1,
              fun _ _ u1 v1 h0 h1 => ?_, ?_, ?_, ?_⟩
            · cases h0; exact hs_not1 u1 v1 h1
            · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, hr0, hr6]
            · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, hr0, hm1]
            · ext u'
              rcases eq_or_ne u' u with rfl | hu'
              · simp [slotsState, v_fin]
              · simp [hs_eq, slotsState, hu']
          · simpa [y, xu₅, xu₄, xu₃, xu₂, x₁, hr0] using hmod_write0 (xu₅.regs 6)
        | some uv0 =>
          rcases uv0 with ⟨u0, v0⟩
          cases e1 with
          | some uv1 =>
            rcases uv1 with ⟨u1, v1⟩
            exfalso
            have hcard2 : 2 ≤ (Dictionary.dom s).card :=
              hs_eq ▸ two_le_card_dom_slotsState v0 v1 (hdisj u0 v0 u1 v1 rfl rfl)
            have hsu_none : s u = none := hs_eq ▸ slotsState_none_of_ne_tags hk0 hk1
            rcases hval.1 with hlt2 | hisSome
            · omega
            · simp [hsu_none] at hisSome
          | none =>
            have hc_z0 : ¬(Cond.eq (8 : Fin 9) 3).Holds xu₅ := by
              change xu₅.regs 8 ≠ xu₅.regs 3
              have hr8_eq : xu₅.regs 8 = xu₃.regs 8 := by simp [xu₅, xu₄]
              rw [hr8_eq, show xu₃.regs 8 = slotKeyTag (some (u0, v0)) from hxu₃_tag0]
              simp [xu₅, xu₄, xu₃, xu₂, x₁, hr3, slotKeyTag]
            let y := xu₅.write (xu₅.regs 7) (xu₅.regs 6)
            have he_ins : ExecWithin w twoSlotInsertCode xu₃ y 9 :=
              (ExecWithin.branch_neg hc0 (he_l1.seq (ExecWithin.branch_neg hc1
                (ExecWithin.branch_neg hc_z0 ExecWithin.store)))).mono (by omega)
            refine ⟨y,
              (hs1.seq (ExecWithin.branch_neg hc_not_q
                (he_pre.seq (ExecWithin.branch_pos hc_ins he_ins)))).mono (by omega),
              rfl, ?_, ?_⟩
            · refine ⟨hwrite_bdd hxu₅_bdd _ _ (hxu₅_bdd.1 6), fun _ => hr0, some (u0, v0),
                some (u, v_fin), fun _ _ _ _ h0 h1 => ?_, ?_, ?_, ?_⟩
              · cases h0; cases h1; exact (hs_not0 u0 v0 rfl).symm
              · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4, hm0]
              · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4, hr6]
              · ext u'
                have hne0 := hs_not0 u0 v0 rfl
                rcases eq_or_ne u' u with rfl | hu'
                · simp [slotsState, hne0, v_fin]
                · simp [hs_eq, slotsState, hu']
            · simpa [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4] using
                hmod_write1 (xu₅.regs 6)
  | delete u =>
    have hr1 : x.regs 1 = 2 := by simpa [twoSlotEncode] using hmatch 1 (by decide)
    have hr2 : x.regs 2 = u.1 + 1 := by simpa [twoSlotEncode] using hmatch 2 (by decide)
    have hc_not_q : ¬(Cond.eq (1 : Fin 9) 3).Holds x₁ := by simp [x₁, hr1, hr3]
    have hc_not_ins : ¬(Cond.eq (1 : Fin 9) 4).Holds xu₃ := by simp [xu₃, xu₂, x₁, hr1, hr4]
    by_cases hk0 : slotKeyTag e0 = u.1 + 1
    · cases e0 with
      | none => simp [slotKeyTag] at hk0
      | some uv0 =>
        rcases uv0 with ⟨u0, v0⟩
        have hu_eq : u = u0 := Fin.ext (by simpa [slotKeyTag] using hk0.symm)
        subst hu_eq
        have hc0 : (Cond.eq (8 : Fin 9) 2).Holds xu₃ := by
          change xu₃.regs 8 = xu₃.regs 2
          rw [hxu₃_tag0]; simp [xu₃, xu₂, x₁, hr2, slotKeyTag]
        let y := xu₃.write (xu₃.regs 0) (xu₃.regs 3)
        have he_del : ExecWithin w twoSlotDeleteCode xu₃ y 2 :=
          ExecWithin.branch_pos hc0 ExecWithin.store
        refine ⟨y,
          (hs1.seq (ExecWithin.branch_neg hc_not_q
            (he_pre.seq (ExecWithin.branch_neg hc_not_ins he_del)))).mono (by omega),
          rfl, ?_, ?_⟩
        · refine ⟨hwrite_bdd hxu₃_bdd _ _ (hxu₃_bdd.1 3), fun _ => hr0,
            ⟨none, ⟨e1, ?_, ?_, ?_, ?_⟩⟩⟩
          · rintro _ _ _ _ ⟨⟩
          · simp [y, xu₃, xu₂, x₁, hr0, hr3, encodeSlot]
          · simp [y, xu₃, xu₂, x₁, hr0, hm1]
          · ext u'
            cases e1 with
            | none =>
              rcases eq_or_ne u' u with rfl | hu'
              · simp [slotsState]
              · simp [hs_eq, slotsState, hu']
            | some uv1 =>
              rcases uv1 with ⟨u1, v1⟩
              have hne01 : u ≠ u1 := hdisj u v0 u1 v1 rfl rfl
              rcases eq_or_ne u' u with rfl | hu'
              · simp [slotsState, hne01]
              · simp [hs_eq, slotsState, hu']
        · simpa [y, xu₃, xu₂, x₁, hr0] using hmod_write0 (xu₃.regs 3)
    · have hc0 : ¬(Cond.eq (8 : Fin 9) 2).Holds xu₃ := by
        change xu₃.regs 8 ≠ xu₃.regs 2
        rw [hxu₃_tag0]; simpa [xu₃, xu₂, x₁, hr2] using hk0
      have hs_not0 : ∀ u0 v0, e0 = some (u0, v0) → u ≠ u0 := by
        rintro u0 v0 rfl h_eq; subst h_eq; exact hk0 rfl
      by_cases hk1 : slotKeyTag e1 = u.1 + 1
      · cases e1 with
        | none => simp [slotKeyTag] at hk1
        | some uv1 =>
          rcases uv1 with ⟨u1, v1⟩
          have hu_eq : u = u1 := Fin.ext (by simpa [slotKeyTag] using hk1.symm)
          subst hu_eq
          have hc1 : (Cond.eq (1 : Fin 9) 2).Holds xu₅ := by
            change xu₅.regs 1 = xu₅.regs 2
            rw [hxu₅_tag1]; simp [xu₅, xu₄, xu₃, xu₂, x₁, hr2, slotKeyTag]
          let y := xu₅.write (xu₅.regs 7) (xu₅.regs 3)
          have he_del : ExecWithin w twoSlotDeleteCode xu₃ y 6 :=
            (ExecWithin.branch_neg hc0
              (he_l1.seq (ExecWithin.branch_pos hc1 ExecWithin.store))).mono (by omega)
          refine ⟨y,
            (hs1.seq (ExecWithin.branch_neg hc_not_q
              (he_pre.seq (ExecWithin.branch_neg hc_not_ins he_del)))).mono (by omega),
            rfl, ?_, ?_⟩
          · refine ⟨hwrite_bdd hxu₅_bdd _ _ (hxu₅_bdd.1 3), fun _ => hr0,
              ⟨e0, ⟨none, ?_, ?_, ?_, ?_⟩⟩⟩
            · rintro _ _ _ _ _ ⟨⟩
            · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4, hm0]
            · simp [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr3, hr4, encodeSlot]
            · ext u'
              cases e0 with
              | none =>
                rcases eq_or_ne u' u with rfl | hu'
                · simp [slotsState]
                · simp [hs_eq, slotsState, hu']
              | some uv0 =>
                rcases uv0 with ⟨u0, v0⟩
                have hne0 := hs_not0 u0 v0 rfl
                rcases eq_or_ne u' u with rfl | hu'
                · simp [slotsState, hne0]
                · simp [hs_eq, slotsState, hu']
          · simpa [y, xu₅, xu₄, xu₃, xu₂, x₁, BinOp.eval, hr0, hr4] using
              hmod_write1 (xu₅.regs 3)
      · have hc1 : ¬(Cond.eq (1 : Fin 9) 2).Holds xu₅ := by
          change xu₅.regs 1 ≠ xu₅.regs 2
          rw [hxu₅_tag1]; simpa [xu₅, xu₄, xu₃, xu₂, x₁, hr2] using hk1
        let y := xu₅.set 8 (xu₅.regs 3)
        have he_del : ExecWithin w twoSlotDeleteCode xu₃ y 7 :=
          (ExecWithin.branch_neg hc0
            (he_l1.seq (ExecWithin.branch_neg hc1 ExecWithin.copy))).mono (by omega)
        refine ⟨y,
          (hs1.seq (ExecWithin.branch_neg hc_not_q
            (he_pre.seq (ExecWithin.branch_neg hc_not_ins he_del)))).mono (by omega),
          rfl, ?_, Modifies.refl _ _⟩
        refine ⟨hxu₅_bdd.set (hxu₅_bdd.1 3), fun _ => hr0, e0, e1, hdisj, hm0, hm1, ?_⟩
        ext u'
        rcases eq_or_ne u' u with rfl | hu'
        · have hs_u : s u' = none := hs_eq ▸ slotsState_none_of_ne_tags hk0 hk1
          simp [hs_u, ← hs_eq]
        · simp [hu', ← hs_eq]

private theorem twoSlotRep_empty {U V w base : ℕ} {usePersBase : Bool} {z : Data 9}
    (hbdd : z.Bounded w) (hr0 : usePersBase = true → z.regs 0 = base)
    (hm0 : z.mem base = 0) (hm1 : z.mem (base + 1) = 0) :
    TwoSlotRep U V w base usePersBase (Dictionary.empty U) z := by
  refine ⟨hbdd, hr0, none, none, ?_, hm0, hm1, rfl⟩
  rintro _ _ _ _ ⟨⟩

private theorem twoSlotRep_supported {U V w base : ℕ} {usePersBase : Bool}
    {s : Dictionary.State U} {x x' : Data 9}
    (hreg : ∀ i : Fin 9, (twoSlotDetCode base usePersBase).input i = false →
      x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base 2).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w) (hrep : TwoSlotRep U V w base usePersBase s x) :
    TwoSlotRep U V w base usePersBase s x' := by
  rcases hrep with ⟨_, hr0, e0, e1, hdisj, hm0, hm1, hs_eq⟩
  have hfp0 : base ∈ (Block.mk base 2).footprint := by simp [Block.mem_footprint, Block.Owns]
  have hfp1 : base + 1 ∈ (Block.mk base 2).footprint := by simp [Block.mem_footprint, Block.Owns]
  refine ⟨hbdd, fun htrue => ?_, e0, e1, hdisj, (hmem base hfp0).trans hm0,
    (hmem (base + 1) hfp1).trans hm1, hs_eq⟩
  have hin0 : (twoSlotDetCode base usePersBase).input 0 = false := by simp [twoSlotDetCode, htrue]
  exact (hreg 0 hin0).trans (hr0 htrue)

/-- Parametric deterministic `WordRAM.StateTransitionImpl` for `Dynamic.spec U V 2` (`space = 2`,
`charge = 16`, `initPotential = 0`), supporting both `persistentRegCount = 0`
(`usePersBase = false`) and `persistentRegCount = 1` (`usePersBase = true`). -/
def twoSlotDetImpl {U V w base : ℕ} (usePersBase : Bool)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hw : 2 ≤ w) (hUV : (U + 1) * V ≤ 2 ^ w)
    (hbase : Fits w (base + 2)) :
    DataStructure.WordRAM.StateTransitionImpl (twoSlotDetCode base usePersBase)
      (Dynamic.spec U V 2) w base Fin.elim0 (Dictionary.empty U) :=
  DataStructure.WordRAM.StateTransitionImpl.ofFn
    (space := 2) (spanTime := 2) (setupTime := 1) (initPotential := 0)
    (charge := fun _ _ => 16)
    (rep := TwoSlotRep U V w base usePersBase)
    (potential := fun _ => 0)
    (encode := twoSlotEncode U V base)
    (argMatch := fun o regs =>
      (usePersBase = false → regs 0 = base) ∧ twoSlotArgMatch U V base o regs)
    (decode := twoSlotDecode)
    (bounded := fun h => h.1)
    (arguments_fit := twoSlot_arguments_fit usePersBase hU hV hw hUV hbase)
    (encode_matches := fun o regs => by
      refine ⟨fun hfalse => by simp [twoSlotDetCode, twoSlotEncode, hfalse], fun i hi => ?_⟩
      cases usePersBase <;> simp [twoSlotDetCode, hi.1])
    (rep_supported := twoSlotRep_supported)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by dsimp [twoSlotDetCode]; decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      change Data.put w x 2 (x.regs 2 + x.regs 4) = some (x.set 2 (x.regs 2 + 1))
      change x.regs 4 = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun {_} _ hfr _ => by
      obtain ⟨_, _, _, _, _, hfb2⟩ := fits_from_params hU hw hUV hbase
      refine ⟨_, (Exec.copy.within).seq (Exec.const hfb2).within,
        rfl, ?_, by simp [twoSlotDetCode, Data.set], fun j => Fin.elim0 j⟩
      simpa [twoSlotDetCode, Data.set] using hfr)
    (setup_exec := fun {x₁} hbdd₁ hb₁ hfr₁ _ hzero => by
      have hfp0 : base ∈ (Block.mk base 2).footprint := by simp [Block.mem_footprint, Block.Owns]
      have hfp1 : base + 1 ∈ (Block.mk base 2).footprint := by
        simp [Block.mem_footprint, Block.Owns]
      refine ⟨x₁.set 3 0, (Exec.const (fits_zero w)).within,
        by simpa [twoSlotDetCode, Data.set] using hfr₁,
        twoSlotRep_empty (hbdd₁.set (fits_zero w))
          (fun _ => by simpa [twoSlotDetCode, Data.set] using hb₁)
          (by simpa [Data.set] using hzero base hfp0)
          (by simpa [Data.set] using hzero (base + 1) hfp1),
        Nat.le_refl 0, Modifies.refl _ _⟩)
    (step_exec := fun {s x} o hrep hval ⟨hr0_f, hmatch⟩ => by
      have hr0 : x.regs 0 = base := by
        cases hup : usePersBase
        · exact hr0_f hup
        · exact hrep.2.1 hup
      obtain ⟨y, ⟨steps, hsteps, hex⟩, hdec, hrep', hmod⟩ :=
        twoSlotBody_exec usePersBase hU hV hw hUV hbase o hrep hval hr0 hmatch
      exact ⟨y, steps, hex, hdec, hrep', hmod, by omega⟩)

/-- Parametric coin-flipping (`Code.rand 8 4`, `¬Code.IsRandFree`) zero-error
`WordRAM.Randomized.StateTransitionImpl` for `Dynamic.spec U V 2` (`space = 2`, `charge = 17`,
`initPotential = 0`). -/
noncomputable def twoSlotRandImpl {U V w base : ℕ} (usePersBase : Bool)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hw : 2 ≤ w) (hUV : (U + 1) * V ≤ 2 ^ w)
    (hbase : Fits w (base + 2)) :
    DataStructure.WordRAM.Randomized.StateTransitionImpl (twoSlotRandCode base usePersBase)
      (Dynamic.spec U V 2) w base Fin.elim0 (Dictionary.empty U) :=
  DataStructure.WordRAM.Randomized.StateTransitionImpl.ofFn
    (Seed := Unit) (seedLaw := PMF.pure ()) (seedSlack := 1)
    (space := 2) (spanTime := 2) (setupTime := 1) (initPotential := 0)
    (charge := fun _ _ => 17)
    (rep := fun _ s x => TwoSlotRep U V w base usePersBase s x)
    (potential := fun _ _ => 0)
    (encode := twoSlotEncode U V base)
    (argMatch := fun o regs =>
      (usePersBase = false → regs 0 = base) ∧ twoSlotArgMatch U V base o regs)
    (decode := twoSlotDecode)
    (bounded := fun h => h.1)
    (arguments_fit := twoSlot_arguments_fit usePersBase hU hV hw hUV hbase)
    (encode_matches := fun o regs => by
      refine ⟨fun hfalse => by simp [twoSlotRandCode, twoSlotDetCode, twoSlotEncode, hfalse],
        fun i hi => ?_⟩
      cases usePersBase <;> simp [twoSlotRandCode, twoSlotDetCode, hi.1])
    (rep_supported := twoSlotRep_supported)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by dsimp [twoSlotRandCode, twoSlotDetCode]; decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      change Data.put w x 2 (x.regs 2 + x.regs 4) = some (x.set 2 (x.regs 2 + 1))
      change x.regs 4 = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun {_} _ hfr _ => by
      obtain ⟨_, _, _, _, _, hfb2⟩ := fits_from_params hU hw hUV hbase
      refine ⟨_, (Exec.copy.within).seq (Exec.const hfb2).within,
        rfl, ?_, by simp [twoSlotRandCode, twoSlotDetCode, Data.set], fun j => Fin.elim0 j⟩
      simpa [twoSlotRandCode, twoSlotDetCode, Data.set] using hfr)
    (setup_exec := fun {x₁} hbdd₁ hb₁ hfr₁ _ hzero => by
      have hfp0 : base ∈ (Block.mk base 2).footprint := by simp [Block.mem_footprint, Block.Owns]
      have hfp1 : base + 1 ∈ (Block.mk base 2).footprint := by
        simp [Block.mem_footprint, Block.Owns]
      refine ⟨PMF.pure ((), x₁.set 3 0),
        by simpa [twoSlotRandCode, twoSlotDetCode] using
          ExecCodeDist.of_execWithin (Exec.const (fits_zero w)).within,
        fun θ => by cases θ; simp,
        fun p hp => ?_⟩
      rw [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨by simpa [twoSlotRandCode, twoSlotDetCode, Data.set] using hfr₁,
        twoSlotRep_empty (hbdd₁.set (fits_zero w))
          (fun _ => by simpa [twoSlotRandCode, twoSlotDetCode, Data.set] using hb₁)
          (by simpa [Data.set] using hzero base hfp0)
          (by simpa [Data.set] using hzero (base + 1) hfp1),
        Nat.le_refl 0, Modifies.refl _ _⟩)
    (step_exec := fun {s} o ν hval _ hsupp => by
      classical
      let runDet : Data 9 → Data 9 := fun z =>
        if hz : TwoSlotRep U V w base usePersBase s z ∧ z.regs 0 = base ∧
            twoSlotArgMatch U V base o z.regs then
          Classical.choose (twoSlotBody_exec usePersBase hU hV hw hUV hbase o hz.1 hval hz.2.1
            hz.2.2)
        else z
      let coinOut : Data 9 → PMF (Data 9) := fun x =>
        (ProbComp.unifFin (x.regs 4)).eval.map fun sample => runDet (x.set 8 sample.val)
      refine ⟨fun p => (coinOut p.2).map fun y => ((), y), fun _ => 17,
        fun p hp => ?_,
        fun θ' => by
          cases θ'
          simp only [one_mul, PMF.pure_apply, ↓reduceIte]
          exact PMF.coe_le_one _ (),
        ?_⟩
      · obtain ⟨hrep, hr0_f, hmatch⟩ := hsupp p hp
        have hr0 : p.2.regs 0 = base := by
          cases hup : usePersBase
          · exact hr0_f hup
          · exact hrep.2.1 hup
        have hfit4 : Fits w (p.2.regs 4) := hrep.1.1 4
        have hrand : ExecCodeDist (B := .standard) w (.rand 8 4) p.2
            ((ProbComp.unifFin (p.2.regs 4)).eval.map fun sample => p.2.set 8 sample.val) 1 := by
          have hr := ExecCodeDist.of_execRand
            (ExecRand.rand (B := .standard) (dst := 8) (src := 4) hfit4)
          refine hr.congr_dist ?_ ?_
          · simp [ProbComp.eval_map, PMF.map]
          · rw [ProbComp.expect_bind]
            simp [ProbComp.expect_pure]
        have hbody_each : ∀ sample : Fin (p.2.regs 4 + 1),
            TwoSlotRep U V w base usePersBase s (p.2.set 8 sample.val) ∧
              (p.2.set 8 sample.val).regs 0 = base ∧
              twoSlotArgMatch U V base o (p.2.set 8 sample.val).regs := by
          intro sample
          have hfs : Fits w sample.val := lt_of_le_of_lt (Nat.le_of_lt_succ sample.2) hfit4
          refine ⟨⟨hrep.1.set hfs, fun hup => by simpa [Data.set] using hrep.2.1 hup, hrep.2.2⟩,
            by simpa [Data.set] using hr0,
            fun i hi => ?_⟩
          have hi8 : i ≠ 8 := fun h => by subst h; omega
          simpa [Data.set, hi8] using hmatch i hi
        let μ₁ : PMF (Data 9) :=
          (ProbComp.unifFin (p.2.regs 4)).eval.map fun sample => p.2.set 8 sample.val
        have hseq := hrand.seq (μ₂ := fun z => PMF.pure (runDet z)) (T₂ := fun _ => 16)
          fun z hz => by
            rw [PMF.mem_support_map_iff] at hz
            obtain ⟨sample, _, rfl⟩ := hz
            have hbz := hbody_each sample
            have hspec := Classical.choose_spec
              (twoSlotBody_exec usePersBase hU hV hw hUV hbase o hbz.1 hval hbz.2.1 hbz.2.2)
            have hrd : runDet (p.2.set 8 sample.val) =
                Classical.choose (twoSlotBody_exec usePersBase hU hV hw hUV hbase o hbz.1 hval
                  hbz.2.1 hbz.2.2) := by
              dsimp only [runDet]; exact dite_eq_left_of_eq_true (eq_true hbz)
            rw [hrd]
            simpa using ExecCodeDist.of_execWithin hspec.1
        refine ⟨?_, fun q hq => ?_⟩
        · refine hseq.congr_dist ?_ ?_
          · rw [PMF.map_comp]
            have hid : (Prod.snd ∘ fun y : Data 9 => ((), y)) = id := rfl
            rw [hid, PMF.map_id]
            dsimp only [coinOut, μ₁]
            simp [PMF.map, Function.comp_def]
          · rw [ENNReal.tsum_mul_right, μ₁.tsum_coe, one_mul]
            norm_num
        · rw [PMF.mem_support_map_iff] at hq
          obtain ⟨y, hy, rfl⟩ := hq
          dsimp only [coinOut] at hy
          rw [PMF.mem_support_map_iff] at hy
          obtain ⟨sample, _, rfl⟩ := hy
          have hbz := hbody_each sample
          have hspec := Classical.choose_spec
            (twoSlotBody_exec usePersBase hU hV hw hUV hbase o hbz.1 hval hbz.2.1 hbz.2.2)
          have hrd : runDet (p.2.set 8 sample.val) =
              Classical.choose (twoSlotBody_exec usePersBase hU hV hw hUV hbase o hbz.1 hval
                hbz.2.1 hbz.2.2) := by
            dsimp only [runDet]; exact dite_eq_left_of_eq_true (eq_true hbz)
          rw [hrd]
          exact ⟨hspec.2.1, hspec.2.2.1, by simpa [Data.set] using hspec.2.2.2⟩
      · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
        rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
        norm_num)

/-! ### 1B. Sequential Execution & Probe-Free `[Instr.halt retReg]` Refutation Sanity Checks -/

/-- Explicit 7-operation regression trace over `Dynamic.Op 4`. -/
def sampleTwoSlotTrace : List (Dynamic.Op 4) :=
  [.insert 0 1, .insert 3 0, .query 0, .delete 0, .insert 2 1, .query 0, .query 2]

/-- End-to-end sequential execution check (`initFresh → insert → insert → query → delete → insert →
query → query`) for both `twoSlotDetImpl false` (`base = 0`, `persistentRegCount = 0`) and
`twoSlotDetImpl true` (`base = 2`, `persistentRegCount = 1`), alongside confirmation that
`twoSlotRandCode` genuinely uses `Code.rand` (`¬Code.IsRandFree`). -/
theorem twoSlot_trace_and_rand_sanity :
    let h0 := mkInitData0_spec (twoSlotDetCode 0 false) Fin.elim0 (fits_zero 4)
    let C0 := twoSlotDetImpl (U := 4) (V := 2) (w := 4) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
    let sim0 := C0.toCellProbe h0.1 h0.2.1 h0.2.2.1
    let h1 := mkInitData0_spec (twoSlotDetCode 2 true) Fin.elim0 (by decide : Fits 4 2)
    let C1 := twoSlotDetImpl (U := 4) (V := 2) (w := 4) (base := 2) true
      (by decide) (by decide) (by decide) (by decide) (by decide)
    let sim1 := C1.toCellProbe h1.1 h1.2.1 h1.2.2.1
    ¬(twoSlotRandCode 0 false).code.IsRandFree ∧
      (sim0.1.runSeq sampleTwoSlotTrace).1 =
        [⟨.insert 0 1, ()⟩, ⟨.insert 3 0, ()⟩, ⟨.query 0, some 1⟩, ⟨.delete 0, ()⟩,
          ⟨.insert 2 1, ()⟩, ⟨.query 0, none⟩, ⟨.query 2, some 1⟩] ∧
      (sim1.1.runSeq sampleTwoSlotTrace).1 =
        [⟨.insert 0 1, ()⟩, ⟨.insert 3 0, ()⟩, ⟨.query 0, some 1⟩, ⟨.delete 0, ()⟩,
          ⟨.insert 2 1, ()⟩, ⟨.query 0, none⟩, ⟨.query 2, some 1⟩] := by
  intro h0 C0 sim0 h1 C1 sim1
  have hv : (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) sampleTwoSlotTrace := by
    dsimp [sampleTwoSlotTrace, Dynamic.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dynamic.valid, Dynamic.step, Dictionary.empty]
    refine ⟨⟨Or.inl (by decide), by decide⟩, ⟨Or.inl (by decide), by decide⟩,
      trivial, trivial, ⟨Or.inl (by decide), by decide⟩, trivial, trivial, trivial⟩
  have hexp :
      ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) sampleTwoSlotTrace).2 =
        [⟨.insert 0 1, ()⟩, ⟨.insert 3 0, ()⟩, ⟨.query 0, some 1⟩, ⟨.delete 0, ()⟩,
          ⟨.insert 2 1, ()⟩, ⟨.query 0, none⟩, ⟨.query 2, some 1⟩] := by
    simp [sampleTwoSlotTrace, Dynamic.spec, StateTransitionSpec.run,
      StateTransitionSpec.ofFn, Dynamic.step]
  exact ⟨by decide, ((sim0.2.1.runSeq_ofFn sampleTwoSlotTrace hv).1).trans hexp,
    ((sim1.2.1.runSeq_ofFn sampleTwoSlotTrace hv).1).trans hexp⟩

/-- Sanity check via `expectedFlatTime_ge_of_indexedScheme` and
`ExecFlatProgramOps.tighten_actualBodyTime`: a probe-free `[Instr.halt retReg]` flat program with
`0`-step budget cannot realize `ExecFlatProgramOps` on `validHistoriesUpTo 4 2 2 9`. -/
theorem not_execFlatProgramOps_halt_zero_time
    {B : Basis} {r w base space : ℕ} {input : Fin r → Bool} {Latent : Type}
    (retReg : Fin r)
    (encode : Dynamic.Op 4 → Fin r → ℕ)
    (decode : (o : Dynamic.Op 4) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex : ∀ ops ∈ validHistoriesUpTo 4 2 2 9, ∃ ν_final,
      ExecFlatProgramOps (Dynamic.spec 4 2 2) Latent w base space
        ([Instr.halt retReg] : Program B r) input encode decode
        (Dictionary.empty 4) ops ν₀ ν_final 0) :
    False := by
  have htr := expectedFlatTime_ge_of_indexedScheme (U := 4) (V := 2) (n := 2)
    (S_max := space + persCount input)
    (by decide) (by decide) (by decide) le_rfl
    ([Instr.halt retReg] : Program B r) encode decode ν₀ hsupp₀
    (fun ops hops => by obtain ⟨ν_f, h⟩ := hex ops hops; exact ⟨ν_f, 0, by simp, h⟩)
    (LB := 1)
    fun {D_det} hcorr => by
      have hl := det_expectedSeqProbes_ge_linear true (U := 4) (V := 2) (n := 2)
        (by decide) (by decide) (D_det := D_det) hcorr
      rw [modeDist_true] at hl
      norm_num at hl
      exact hl
  have hzero :
      (∑' ops, insertQueryDeleteDist 4 2 2 (by decide) (by decide) ops *
        flatExpectedBodyTime w ([Instr.halt retReg] : Program B r) input encode
          (ν₀.map Prod.snd) ops) ≤ 0 := by
    refine (Cslib.Probability.PMF.tsum_mul_le_of_support _ fun ops hops => ?_)
    obtain ⟨hv, _⟩ := validHistory_of_mem_support_insertQueryDeleteDist hops
    have hlen := length_of_mem_support_insertQueryDeleteDist hops
    obtain ⟨ν_f, h⟩ := hex ops ⟨hv, by omega⟩
    exact h.flatExpectedBodyTime_le
  have hbot := htr.trans hzero
  simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hbot
  have hpos : (0 : ℝ) < (1 : ℝ) / (2 * (persCount input : ℝ) + 1) := by positivity
  linarith

/-- End-to-end check of the **actual-time tightening bridge**
(`ExecFlatProgramOps.tighten_actualBodyTime` and `flatExpectedTime_eq_add_length`) on both
`twoSlotDetImpl` and `twoSlotRandImpl` across `sampleTwoSlotTrace` (7 operations): verifies that
an arbitrary certified `ExecFlatProgramOps` execution admits the exact intrinsic expected body
count `flatExpectedBodyTime` (bounded by the certified `totalCost` budget, with
`flatExpectedTime = flatExpectedBodyTime + 7`) while preserving the `Data 9` final marginal
`flatStateDist`. -/
theorem twoSlot_actualTime_bridge_sanity :
    let C_det := (twoSlotDetImpl (U := 4) (V := 2) (w := 4) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    let C_rand := twoSlotRandImpl (U := 4) (V := 2) (w := 4) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
    let p_det := (twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output
    let p_rand := (twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output
    (∃ ν₀ ν_final : PMF (C_det.Seed × Data 9),
      let body := flatExpectedBodyTime 4 p_det (twoSlotDetCode 0 false).input C_det.encode
        (ν₀.map Prod.snd) sampleTwoSlotTrace
      let total := flatExpectedTime 4 p_det (twoSlotDetCode 0 false).input C_det.encode
        (ν₀.map Prod.snd) sampleTwoSlotTrace
      ExecFlatProgramOps (Dynamic.spec 4 2 2) C_det.Seed 4 0 2 p_det
        (twoSlotDetCode 0 false).input C_det.encode (fun o _ regs => C_det.decode o regs)
        (Dictionary.empty 4) sampleTwoSlotTrace ν₀ ν_final body ∧
      body ≤ (C_det.initPotential : ℝ≥0∞) +
        ((Dynamic.spec 4 2 2).totalCost C_det.charge (Dictionary.empty 4) sampleTwoSlotTrace :
          ℝ≥0∞) ∧
      total = body + 7 ∧
      ν_final.map Prod.snd = flatStateDist 4 p_det (twoSlotDetCode 0 false).input C_det.encode
        (ν₀.map Prod.snd) sampleTwoSlotTrace) ∧
    (∃ ν₀ ν_final : PMF (C_rand.Seed × Data 9),
      let body := flatExpectedBodyTime 4 p_rand (twoSlotRandCode 0 false).input C_rand.encode
        (ν₀.map Prod.snd) sampleTwoSlotTrace
      let total := flatExpectedTime 4 p_rand (twoSlotRandCode 0 false).input C_rand.encode
        (ν₀.map Prod.snd) sampleTwoSlotTrace
      ExecFlatProgramOps (Dynamic.spec 4 2 2) C_rand.Seed 4 0 2 p_rand
        (twoSlotRandCode 0 false).input C_rand.encode (fun o _ regs => C_rand.decode o regs)
        (Dictionary.empty 4) sampleTwoSlotTrace ν₀ ν_final body ∧
      body ≤ (C_rand.initPotential : ℝ≥0∞) +
        ((Dynamic.spec 4 2 2).totalCost C_rand.charge (Dictionary.empty 4) sampleTwoSlotTrace :
          ℝ≥0∞) ∧
      total = body + 7 ∧
      ν_final.map Prod.snd = flatStateDist 4 p_rand (twoSlotRandCode 0 false).input C_rand.encode
        (ν₀.map Prod.snd) sampleTwoSlotTrace) := by
  intro C_det C_rand p_det p_rand
  have hv : (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) sampleTwoSlotTrace := by
    dsimp [sampleTwoSlotTrace, Dynamic.spec, StateTransitionSpec.ValidHistory,
      StateTransitionSpec.ofFn, Dynamic.valid, Dynamic.step, Dictionary.empty]
    refine ⟨⟨Or.inl (by decide), by decide⟩, ⟨Or.inl (by decide), by decide⟩,
      trivial, trivial, ⟨Or.inl (by decide), by decide⟩, trivial, trivial, trivial⟩
  have hlen : (sampleTwoSlotTrace.length : ℝ≥0∞) = 7 := by simp [sampleTwoSlotTrace]
  obtain ⟨ν_d, _, hsteps_d⟩ :=
    exists_flat_exec_of_stateTransitionImpl C_det (fits_zero 4) nofun nofun nofun
  obtain ⟨hle_d, _, ν_fd, hex_d⟩ := hsteps_d sampleTwoSlotTrace hv
  obtain ⟨ν_r, _, hsteps_r⟩ :=
    exists_flat_exec_of_stateTransitionImpl C_rand (fits_zero 4) nofun nofun nofun
  obtain ⟨hle_r, _, ν_fr, hex_r⟩ := hsteps_r sampleTwoSlotTrace hv
  exact ⟨⟨ν_d, ν_fd, hex_d, hle_d,
      by rw [flatExpectedTime_eq_add_length, hlen], hex_d.tighten_actualBodyTime.2.2⟩,
    ⟨ν_r, ν_fr, hex_r, hle_r,
      by rw [flatExpectedTime_eq_add_length, hlen], hex_r.tighten_actualBodyTime.2.2⟩⟩

/-! ### 2. Concrete Client Instantiations of All 4 Generic Word-RAM Transfer Bridges -/

private theorem validHist_flatExec_of_steps {B : Basis} {U V n M r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
    (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base params
      (Dictionary.empty U))
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, p.2.mem a = 0) ∧
      (∀ ops ∈ validHistoriesUpTo U V n M,
        flatExpectedBodyTime w (P.code.program P.output) P.input C.encode (ν₀.map Prod.snd) ops
          ≠ ⊤ ∧
        ∃ ν_final,
          ExecFlatProgramOps (Dynamic.spec U V n) C.Seed w base C.space
            (P.code.program P.output) P.input C.encode (fun o _ regs => C.decode o regs)
            (Dictionary.empty U) ops ν₀ ν_final
            (flatExpectedBodyTime w (P.code.program P.output) P.input C.encode
              (ν₀.map Prod.snd) ops)) ∧
      (∀ ops ∈ validHistoriesUpTo U V n M,
        ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
          ExecFlatProgramOps (Dynamic.spec U V n) C.Seed w base C.space
            (P.code.program P.output) P.input C.encode (fun o _ regs => C.decode o regs)
            (Dictionary.empty U) ops ν₀ ν_final T_ops) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ :=
    exists_flat_exec_of_stateTransitionImpl C hbase hparams_fit hparams_fr hparams_agree
  refine ⟨ν₀, hsupp₀, fun ops hops => (hsteps ops hops.1).2, fun ops hops => ?_⟩
  obtain ⟨_, hfin, ν_f, hex⟩ := hsteps ops hops.1
  exact ⟨ν_f, _, hfin, hex⟩

private theorem linear_lb_iqd {S_max w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op 4) Dynamic.Op.Result S_max w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo 4 2 2 (4 * 2 + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2) :
    (1 : ℝ) ≤ ∑' ops, (insertQueryDeleteDist 4 2 2 (by decide) (by decide) ops).toReal *
      (D_det.seqProbes ops : ℝ) := by
  have hl := det_expectedSeqProbes_ge_linear true (U := 4) (V := 2) (n := 2)
    (by decide) (by decide) (D_det := D_det) hcorr
  rw [modeDist_true] at hl
  norm_num at hl
  exact hl

private theorem linear_lb_upd {S_max w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op 4) Dynamic.Op.Result S_max w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo 4 2 2 (3 * 2 + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2) :
    (1 : ℝ) ≤ ∑' ops, (insertDeleteDist 4 2 2 (by decide) (by decide) ops).toReal *
      (D_det.seqProbes ops : ℝ) := by
  have hl := det_expectedSeqProbes_ge_linear false (U := 4) (V := 2) (n := 2)
    (by decide) (by decide) (D_det := D_det) hcorr
  rw [modeDist_false] at hl
  norm_num at hl
  exact hl

/-- Concrete end-to-end instantiations of all 4 generic dictionary cell-probe-to-Word-RAM transfer
bridges (`expectedFlatTime_ge_of_indexedScheme`, `expectedFlatTime_update_ge_of_indexedScheme`,
`expectedTotalCost_ge_of_indexedScheme` at both `persistentRegCount = 0` and
`persistentRegCount = 1`, and `expectedTotalCost_update_ge_of_indexedScheme`), demonstrating that
deterministic `twoSlotDetImpl` embeds directly via `StateTransitionImpl.toRandomized` without any
initial-state witness `d₀`. -/
theorem all_four_transfer_bridges_concrete :
    let C_det0 := (twoSlotDetImpl (U := 4) (V := 2) (w := 4) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    let C_det1 := (twoSlotDetImpl (U := 4) (V := 2) (w := 4) (base := 2) true
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    let C_rand := twoSlotRandImpl (U := 4) (V := 2) (w := 4) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
    (∃ ν₀ : PMF (C_det0.Seed × Data 9),
      let body := flatExpectedBodyTime 4
        ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
        (twoSlotDetCode 0 false).input C_det0.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 4 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 4 2 2) C_det0.Seed 4 0 2
          ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
          (twoSlotDetCode 0 false).input C_det0.encode (fun o _ regs => C_det0.decode o regs)
          (Dictionary.empty 4) ops ν₀ ν_final (body ops)) ∧
      (1 : ℝ≥0∞) ≤
        ∑' ops, insertQueryDeleteDist 4 2 2 (by decide) (by decide) ops * body ops) ∧
    (∃ ν₀ : PMF (C_rand.Seed × Data 9),
      let body := flatExpectedBodyTime 4
        ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
        (twoSlotRandCode 0 false).input C_rand.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 4 2 2 7, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 4 2 2) C_rand.Seed 4 0 2
          ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
          (twoSlotRandCode 0 false).input C_rand.encode (fun o _ regs => C_rand.decode o regs)
          (Dictionary.empty 4) ops ν₀ ν_final (body ops)) ∧
      (1 : ℝ≥0∞) ≤
        ∑' ops, insertDeleteDist 4 2 2 (by decide) (by decide) ops * body ops) ∧
    ((1 : ℝ≥0∞) ≤ (C_det0.initPotential : ℝ≥0∞) +
      ∑' ops, insertQueryDeleteDist 4 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 4 2 2).totalCost C_det0.charge (Dictionary.empty 4) ops : ℝ≥0∞)) ∧
    (ENNReal.ofReal (1 / 3) ≤ (C_det1.initPotential : ℝ≥0∞) +
      ∑' ops, insertQueryDeleteDist 4 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 4 2 2).totalCost C_det1.charge (Dictionary.empty 4) ops : ℝ≥0∞)) ∧
    ((1 : ℝ≥0∞) ≤ (C_rand.initPotential : ℝ≥0∞) +
      ∑' ops, insertQueryDeleteDist 4 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 4 2 2).totalCost C_rand.charge (Dictionary.empty 4) ops : ℝ≥0∞)) ∧
    ((1 : ℝ≥0∞) ≤ (C_rand.initPotential : ℝ≥0∞) +
      ∑' ops, insertDeleteDist 4 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 4 2 2).totalCost C_rand.charge (Dictionary.empty 4) ops : ℝ≥0∞)) := by
  intro C_det0 C_det1 C_rand
  have hp0 := (persistentRegCount_twoSlot_false 0).1
  have hp1 := (persistentRegCount_twoSlot_true 2).1
  have hpr := (persistentRegCount_twoSlot_false 0).2
  have hpc0 : persCount (twoSlotDetCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hp0]
  have hpcr : persCount (twoSlotRandCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hpr]
  obtain ⟨ν_d, hsupp_d, hreal_d, hcorr_d⟩ :=
    validHist_flatExec_of_steps (M := 9) C_det0 (fits_zero 4) nofun nofun nofun
  obtain ⟨ν_r, hsupp_r, hreal_r, hcorr_r⟩ :=
    validHist_flatExec_of_steps (M := 7) C_rand (fits_zero 4) nofun nofun nofun
  refine ⟨⟨ν_d, hreal_d, ?_⟩, ⟨ν_r, hreal_r, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h := expectedFlatTime_ge_of_indexedScheme (by decide) (by decide) (by decide) le_rfl
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det0.encode (fun o _ regs => C_det0.decode o regs) ν_d hsupp_d hcorr_d linear_lb_iqd
    simpa [hpc0] using h
  · have h := expectedFlatTime_update_ge_of_indexedScheme (by decide) (by decide) (by decide) le_rfl
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r linear_lb_upd
    simpa [hpcr] using h
  · have h := expectedTotalCost_ge_of_indexedScheme (by decide) (by decide) C_det0
      (fits_zero 4) nofun nofun nofun le_rfl linear_lb_iqd
    simpa [hp0] using h
  · have h := expectedTotalCost_ge_of_indexedScheme (by decide) (by decide) C_det1
      (by decide) nofun nofun nofun le_rfl linear_lb_iqd
    rw [hp1] at h; norm_num at h; exact h
  · have h := expectedTotalCost_ge_of_indexedScheme (by decide) (by decide) C_rand
      (fits_zero 4) nofun nofun nofun le_rfl linear_lb_iqd
    simpa [hpr] using h
  · have h := expectedTotalCost_update_ge_of_indexedScheme (by decide) (by decide) C_rand
      (fits_zero 4) nofun nofun nofun le_rfl linear_lb_upd
    simpa [hpr] using h

/-! ### 3. Concrete Non-Vacuity Instantiations of Query-Inclusive Headlines & Corollaries
(`U = 31, V = 2, n = 2, k = 1, w = 6, R = 3 / 2`) -/

private theorem hw_31_2 : ((6 : ℕ) : ℝ) ≤ 2 * (Real.logb 2 (31 : ℕ) + Real.logb 2 (2 : ℕ)) := by
  have hlog31 : (4 : ℝ) ≤ Real.logb 2 (31 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (4 : ℕ)) ≤ (31 : ℝ) by norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
  have hlog2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  push_cast; linarith

private theorem benchmarkBits_31_2_2_ge : (21 / 2 : ℝ) ≤ benchmarkBits 31 2 2 := by
  have hc2 : (31 : ℕ).choose 2 = 465 := by decide
  have hch2 : (17 : ℝ) ≤ 2 * Real.logb 2 ((31 : ℕ).choose 2 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (17 : ℕ)) ≤ (((31 : ℕ).choose 2 : ℝ) ^ (2 : ℕ)) by rw [hc2]; norm_num)
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
      Nat.cast_ofNat, Nat.cast_ofNat] at hl
  have hlog2 : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_ofNat]; exact Real.logb_self_eq_one (by norm_num)
  rw [benchmarkBits_eq, hlog2]; push_cast at hch2 ⊢; linarith

private theorem logb_four_thirds_pos :
    0 < Real.logb 2 (((2 : ℕ) : ℝ) / max (3 / 2 : ℝ) 1) := by
  rw [max_eq_left (by norm_num : (1 : ℝ) ≤ 3 / 2), Nat.cast_ofNat,
    show (2 : ℝ) / (3 / 2 : ℝ) = 4 / 3 by norm_num]
  exact Real.logb_pos (by norm_num) (by norm_num)

/-- Concrete non-vacuity instantiations of **Word-RAM Theorem 1.1 / Theorem 3.1**
(`expectedFlatTime_ge_of_iterLog_redundancy`, including its `k = Nat.logStar 2` `O(n)`-redundancy
specialization) and its certified-budget corollary (`expectedTotalCost_ge_of_iterLog_redundancy`)
on deterministic `twoSlotDetImpl.toRandomized` and coin-flipping `twoSlotRandImpl` at
`(U = 31, V = 2, n = 2, w = 6)`, plus relocated `persistentRegCount = 1` (`base = 2, r_max = 1`).
-/
theorem wordram_theorem1_1_concrete_instantiations :
    let C_det := (twoSlotDetImpl (U := 31) (V := 2) (w := 6) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    let C_rand := twoSlotRandImpl (U := 31) (V := 2) (w := 6) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
    let C_rel := (twoSlotDetImpl (U := 31) (V := 2) (w := 6) (base := 2) true
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    (∃ ν₀ : PMF (C_det.Seed × Data 9),
      let body := flatExpectedBodyTime 6
        ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
        (twoSlotDetCode 0 false).input C_det.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 31 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 31 2 2) C_det.Seed 6 0 2
          ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
          (twoSlotDetCode 0 false).input C_det.encode (fun o _ regs => C_det.decode o regs)
          (Dictionary.empty 31) ops ν₀ ν_final (body ops)) ∧
      ∃ c > 0, ENNReal.ofReal (c * 2) ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops) ∧
    (∃ ν₀ : PMF (C_rand.Seed × Data 9),
      let body := flatExpectedBodyTime 6
        ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
        (twoSlotRandCode 0 false).input C_rand.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 31 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 31 2 2) C_rand.Seed 6 0 2
          ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
          (twoSlotRandCode 0 false).input C_rand.encode (fun o _ regs => C_rand.decode o regs)
          (Dictionary.empty 31) ops ν₀ ν_final (body ops)) ∧
      ∃ c > 0, ENNReal.ofReal (c * 2 * (Nat.logStar 2 : ℝ)) ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops) ∧
    (∃ ν₀ : PMF (C_rel.Seed × Data 9),
      let body := flatExpectedBodyTime 6
        ((twoSlotDetCode 2 true).code.program (twoSlotDetCode 2 true).output)
        (twoSlotDetCode 2 true).input C_rel.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 31 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 31 2 2) C_rel.Seed 6 2 2
          ((twoSlotDetCode 2 true).code.program (twoSlotDetCode 2 true).output)
          (twoSlotDetCode 2 true).input C_rel.encode (fun o _ regs => C_rel.decode o regs)
          (Dictionary.empty 31) ops ν₀ ν_final (body ops)) ∧
      ∃ c > 0, ENNReal.ofReal (c * 2 * (Nat.logStar 2 : ℝ)) ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤ (C_det.initPotential : ℝ≥0∞) +
      ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 31 2 2).totalCost C_det.charge (Dictionary.empty 31) ops : ℝ≥0∞)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤ (C_rand.initPotential : ℝ≥0∞) +
      ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 31 2 2).totalCost C_rand.charge (Dictionary.empty 31) ops : ℝ≥0∞)) := by
  intro C_det C_rand C_rel
  have hp0 := (persistentRegCount_twoSlot_false 0).1
  have hpr := (persistentRegCount_twoSlot_false 0).2
  have hp1 := (persistentRegCount_twoSlot_true 2).1
  have hpc0 : persCount (twoSlotDetCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hp0]
  have hpcr : persCount (twoSlotRandCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hpr]
  have hpc1 : persCount (twoSlotDetCode 2 true).input = 1 := by
    rw [← persistentRegCount_eq_persCount, hp1]
  have hpoly : (2 : ℝ) ^ ((1 : ℝ) + 1) ≤ (31 : ℝ) := by norm_num
  have hk_hi : 1 ≤ Nat.logStar 2 := by decide
  have hsp_iter : (((2 + 0) * 6 : ℕ) : ℝ) ≤
      benchmarkBits 31 2 2 + 1 * (2 : ℝ) * ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by
    have hmax : max (Nat.iterLog 1 2) 1 = 1 := by decide
    rw [hmax]; push_cast; linarith [benchmarkBits_31_2_2_ge]
  have hsp_star : (((2 + 0) * 6 : ℕ) : ℝ) ≤
      benchmarkBits 31 2 2 + 1 * (2 : ℝ) * ((max (Nat.iterLog (Nat.logStar 2) 2) 1 : ℕ) : ℝ) := by
    have hmax : max (Nat.iterLog (Nat.logStar 2) 2) 1 = 1 := by decide
    rw [hmax]; push_cast; linarith [benchmarkBits_31_2_2_ge]
  have hsp_rel : (((2 + 1) * 6 : ℕ) : ℝ) ≤
      benchmarkBits 31 2 2 + 4 * (2 : ℝ) * ((max (Nat.iterLog (Nat.logStar 2) 2) 1 : ℕ) : ℝ) := by
    have hmax : max (Nat.iterLog (Nat.logStar 2) 2) 1 = 1 := by decide
    rw [hmax]; push_cast; linarith [benchmarkBits_31_2_2_ge]
  have hsp_det : C_det.space = 2 := rfl
  have hsp_rand : C_rand.space = 2 := rfl
  obtain ⟨ν_d, hsupp_d, hreal_d, hcorr_d⟩ :=
    validHist_flatExec_of_steps (M := 9) C_det (fits_zero 6) nofun nofun nofun
  obtain ⟨ν_r, hsupp_r, hreal_r, hcorr_r⟩ :=
    validHist_flatExec_of_steps (M := 9) C_rand (fits_zero 6) nofun nofun nofun
  obtain ⟨ν_1, hsupp_1, hreal_1, hcorr_1⟩ :=
    validHist_flatExec_of_steps (M := 9) C_rel (by decide) nofun nofun nofun
  obtain ⟨c₁, hc₁, hf₁⟩ := expectedFlatTime_ge_of_iterLog_redundancy.{0}
    (α := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂, hf₂⟩ := expectedFlatTime_ge_of_iterLog_redundancy.{0}
    (α := 1) (c_R := 4) (c_w := 2) 1 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hb₁⟩ := expectedTotalCost_ge_of_iterLog_redundancy
    (α := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨ν_d, hreal_d, c₁, hc₁, ?_⟩, ⟨ν_r, hreal_r, c₁, hc₁, ?_⟩,
    ⟨ν_1, hreal_1, c₂, hc₂, ?_⟩, ⟨c₃, hc₃, ?_⟩, ⟨c₃, hc₃, ?_⟩⟩
  · have h := hf₁ (by decide) (by decide) hpoly (by decide) le_rfl hk_hi (by omega) hw_31_2
      (by rw [hpc0]; exact hsp_iter)
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det.encode (fun o _ regs => C_det.decode o regs) ν_d hsupp_d hcorr_d
    push_cast at h; rwa [mul_one] at h
  · have h := hf₁ (k := Nat.logStar 2) (by decide) (by decide) hpoly (by decide) hk_hi le_rfl
      (by omega) hw_31_2 (by rw [hpcr]; exact hsp_star)
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r
    push_cast at h; exact h
  · have h := hf₂ (k := Nat.logStar 2) (by decide) (by decide) hpoly (by decide) hk_hi le_rfl
      (by rw [hpc1]) hw_31_2 (by rw [hpc1]; exact hsp_rel)
      ((twoSlotDetCode 2 true).code.program (twoSlotDetCode 2 true).output)
      C_rel.encode (fun o _ regs => C_rel.decode o regs) ν_1 hsupp_1 hcorr_1
    push_cast at h; exact h
  · have h := hb₁ (by decide) (by decide) hpoly (by decide) le_rfl hk_hi (by omega) hw_31_2 C_det
      (by rw [hsp_det, hp0]; exact hsp_iter) (fits_zero 6) nofun nofun nofun
    push_cast at h; rwa [mul_one] at h
  · have h := hb₁ (by decide) (by decide) hpoly (by decide) le_rfl hk_hi (by omega) hw_31_2 C_rand
      (by rw [hsp_rand, hpr]; exact hsp_iter) (fits_zero 6) nofun nofun nofun
    push_cast at h; rwa [mul_one] at h

/-- Concrete non-vacuity instantiations of **Word-RAM Theorem 1.2 / Theorem 6.1** and combined
Theorems 1.1 & 1.2 (`expectedFlatTime_ge_of_sublinear_redundancy`,
`expectedFlatTime_ge_iterLogStar_add_log_div`) and their certified-budget corollaries
(`expectedTotalCost_ge_of_sublinear_redundancy`, `expectedTotalCost_ge_iterLogStar_add_log_div`) at
`(U = 31, V = 2, n = 2, w = 6, R = 3 / 2)` with strictly positive `0 < LB` (`log₂(4 / 3) > 0`), plus
relocated `persistentRegCount = 1` (`base = 2, r_max = 1, R = 8`) on
`expectedFlatTime_ge_iterLogStar_add_log_div`. -/
theorem wordram_theorem1_2_concrete_instantiations :
    let C_det := (twoSlotDetImpl (U := 31) (V := 2) (w := 6) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    let C_rand := twoSlotRandImpl (U := 31) (V := 2) (w := 6) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
    let C_rel_rand := twoSlotRandImpl (U := 31) (V := 2) (w := 6) (base := 2) true
      (by decide) (by decide) (by decide) (by decide) (by decide)
    (∃ ν₀ : PMF (C_det.Seed × Data 9),
      let body := flatExpectedBodyTime 6
        ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
        (twoSlotDetCode 0 false).input C_det.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 31 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 31 2 2) C_det.Seed 6 0 2
          ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
          (twoSlotDetCode 0 false).input C_det.encode (fun o _ regs => C_det.decode o regs)
          (Dictionary.empty 31) ops ν₀ ν_final (body ops)) ∧
      (∃ B > 0, ENNReal.ofReal B ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops) ∧
      (∃ c > 0, ENNReal.ofReal (c * 2 * (1 + Real.logb 2 (4 / 3))) ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops)) ∧
    (∃ ν₀ : PMF (C_rand.Seed × Data 9),
      let body := flatExpectedBodyTime 6
        ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
        (twoSlotRandCode 0 false).input C_rand.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 31 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 31 2 2) C_rand.Seed 6 0 2
          ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
          (twoSlotRandCode 0 false).input C_rand.encode (fun o _ regs => C_rand.decode o regs)
          (Dictionary.empty 31) ops ν₀ ν_final (body ops)) ∧
      (∃ B > 0, ENNReal.ofReal B ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops) ∧
      (∃ c > 0, ENNReal.ofReal (c * 2 * (1 + Real.logb 2 (4 / 3))) ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops)) ∧
    (∃ ν₀ : PMF (C_rel_rand.Seed × Data 9),
      let body := flatExpectedBodyTime 6
        ((twoSlotRandCode 2 true).code.program (twoSlotRandCode 2 true).output)
        (twoSlotRandCode 2 true).input C_rel_rand.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 31 2 2 9, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 31 2 2) C_rel_rand.Seed 6 2 2
          ((twoSlotRandCode 2 true).code.program (twoSlotRandCode 2 true).output)
          (twoSlotRandCode 2 true).input C_rel_rand.encode
          (fun o _ regs => C_rel_rand.decode o regs)
          (Dictionary.empty 31) ops ν₀ ν_final (body ops)) ∧
      ∃ c > 0, ENNReal.ofReal (c * 2) ≤
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops * body ops) ∧
    (∃ B > 0, ENNReal.ofReal B ≤ (C_det.initPotential : ℝ≥0∞) +
      ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops *
        ((Dynamic.spec 31 2 2).totalCost C_det.charge (Dictionary.empty 31) ops : ℝ≥0∞)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2 * (1 + Real.logb 2 (4 / 3))) ≤
      (C_rand.initPotential : ℝ≥0∞) +
        ∑' ops, insertQueryDeleteDist 31 2 2 (by decide) (by decide) ops *
          ((Dynamic.spec 31 2 2).totalCost C_rand.charge (Dictionary.empty 31) ops : ℝ≥0∞)) := by
  intro C_det C_rand C_rel_rand
  have hp0 := (persistentRegCount_twoSlot_false 0).1
  have hpr := (persistentRegCount_twoSlot_false 0).2
  have hpr1 := (persistentRegCount_twoSlot_true 2).2
  have hpc0 : persCount (twoSlotDetCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hp0]
  have hpcr : persCount (twoSlotRandCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hpr]
  have hpcr1 : persCount (twoSlotRandCode 2 true).input = 1 := by
    rw [← persistentRegCount_eq_persCount, hpr1]
  have hpoly : (2 : ℝ) ^ ((1 : ℝ) + 1) ≤ (31 : ℝ) := by norm_num
  have hls2 : Nat.logStar 2 = 1 := by decide
  have hsp_sub : (((2 + 0) * 6 : ℕ) : ℝ) ≤ benchmarkBits 31 2 2 + (3 / 2 : ℝ) := by
    push_cast; linarith [benchmarkBits_31_2_2_ge]
  have hsp_rel : (((2 + 1) * 6 : ℕ) : ℝ) ≤ benchmarkBits 31 2 2 + (8 : ℝ) := by
    push_cast; linarith [benchmarkBits_31_2_2_ge]
  have hsp_det : C_det.space = 2 := rfl
  have hsp_rand : C_rand.space = 2 := rfl
  have hlog_eq : Real.logb 2 (((2 : ℕ) : ℝ) / max (3 / 2 : ℝ) 1) = Real.logb 2 (4 / 3) := by
    rw [max_eq_left (by norm_num : (1 : ℝ) ≤ 3 / 2), Nat.cast_ofNat]
    norm_num
  have hlpos : 0 < Real.logb 2 (4 / 3) := hlog_eq ▸ logb_four_thirds_pos
  obtain ⟨ν_d, hsupp_d, hreal_d, hcorr_d⟩ :=
    validHist_flatExec_of_steps (M := 9) C_det (fits_zero 6) nofun nofun nofun
  obtain ⟨ν_r, hsupp_r, hreal_r, hcorr_r⟩ :=
    validHist_flatExec_of_steps (M := 9) C_rand (fits_zero 6) nofun nofun nofun
  obtain ⟨ν_1, hsupp_1, hreal_1, hcorr_1⟩ :=
    validHist_flatExec_of_steps (M := 9) C_rel_rand (by decide) nofun nofun nofun
  obtain ⟨c₁, hc₁, hf₁⟩ := expectedFlatTime_ge_of_sublinear_redundancy.{0}
    (α := 1) (c_w := 2) 0 (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂, hf₂⟩ := expectedFlatTime_ge_iterLogStar_add_log_div.{0}
    (α := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hf₃⟩ := expectedFlatTime_ge_iterLogStar_add_log_div.{0}
    (α := 1) (c_R := 4) (c_w := 2) 1 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₄, hc₄, hb₁⟩ := expectedTotalCost_ge_of_sublinear_redundancy
    (α := 1) (c_w := 2) 0 (by norm_num) (by norm_num)
  obtain ⟨c₅, hc₅, hb₂⟩ := expectedTotalCost_ge_iterLogStar_add_log_div
    (α := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨ν_d, hreal_d,
      ⟨c₁ * 2 * Real.logb 2 (4 / 3), by positivity, ?_⟩, ⟨c₂, hc₂, ?_⟩⟩,
    ⟨ν_r, hreal_r,
      ⟨c₁ * 2 * Real.logb 2 (4 / 3), by positivity, ?_⟩, ⟨c₂, hc₂, ?_⟩⟩,
    ⟨ν_1, hreal_1, c₃, hc₃, ?_⟩,
    ⟨c₄ * 2 * Real.logb 2 (4 / 3), by positivity, ?_⟩,
    ⟨c₅, hc₅, ?_⟩⟩
  · have h := hf₁ (R := 3 / 2) (by decide) (by decide) hpoly (by decide) (by norm_num) (by omega)
      hw_31_2 (by rw [hpc0]; exact hsp_sub)
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det.encode (fun o _ regs => C_det.decode o regs) ν_d hsupp_d hcorr_d
    rw [hlog_eq] at h; push_cast at h; exact h
  · have h := hf₂ (R := 3 / 2) (by decide) (by decide) hpoly (by decide) (by norm_num) (by omega)
      hw_31_2 (by rw [hpc0]; exact hsp_sub)
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det.encode (fun o _ regs => C_det.decode o regs) ν_d hsupp_d hcorr_d
    rw [hlog_eq, hls2, max_eq_right hlpos.le] at h; push_cast at h; exact h
  · have h := hf₁ (R := 3 / 2) (by decide) (by decide) hpoly (by decide) (by norm_num) (by omega)
      hw_31_2 (by rw [hpcr]; exact hsp_sub)
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r
    rw [hlog_eq] at h; push_cast at h; exact h
  · have h := hf₂ (R := 3 / 2) (by decide) (by decide) hpoly (by decide) (by norm_num) (by omega)
      hw_31_2 (by rw [hpcr]; exact hsp_sub)
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r
    rw [hlog_eq, hls2, max_eq_right hlpos.le] at h; push_cast at h; exact h
  · have h := hf₃ (R := 8) (by decide) (by decide) hpoly (by decide) (by norm_num)
      (by rw [hpcr1]) hw_31_2 (by rw [hpcr1]; exact hsp_rel)
      ((twoSlotRandCode 2 true).code.program (twoSlotRandCode 2 true).output)
      C_rel_rand.encode (fun o _ regs => C_rel_rand.decode o regs) ν_1 hsupp_1 hcorr_1
    refine (ENNReal.ofReal_le_ofReal ?_).trans h
    rw [hls2]; push_cast
    have hnn : 0 ≤ max (0 : ℝ) (Real.logb 2 (2 / max (8 : ℝ) 1)) := le_max_left _ _
    nlinarith
  · have h := hb₁ (R := 3 / 2) (by decide) (by decide) hpoly (by decide) (by norm_num) (by omega)
      hw_31_2 C_det (by rw [hsp_det, hp0]; exact hsp_sub)
      (fits_zero 6) nofun nofun nofun
    rw [hlog_eq] at h; push_cast at h; exact h
  · have h := hb₂ (R := 3 / 2) (by decide) (by decide) hpoly (by decide) (by norm_num) (by omega)
      hw_31_2 C_rand (by rw [hsp_rand, hpr]; exact hsp_sub)
      (fits_zero 6) nofun nofun nofun
    rw [hlog_eq, hls2, max_eq_right hlpos.le] at h; push_cast at h; exact h

/-! ### 4. Concrete Non-Vacuity Instantiations of Theorem 1.3 Headlines & Corollaries
(`U = 15, V = 1024, n = 2, k = 1, w = 14, R = 3 / 2, α_V = 1`) -/

private theorem hw_15_1024 :
    ((14 : ℕ) : ℝ) ≤ 2 * (Real.logb 2 (15 : ℕ) + Real.logb 2 (1024 : ℕ)) := by
  have hlog15 : (3 : ℝ) ≤ Real.logb 2 (15 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (3 : ℕ)) ≤ (15 : ℝ) by norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
  have hlog1024 : Real.logb 2 (1024 : ℝ) = 10 := by
    rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  push_cast; linarith

private theorem benchmarkBits_15_1024_2_ge : (53 / 2 : ℝ) ≤ benchmarkBits 15 1024 2 := by
  have hc2 : (15 : ℕ).choose 2 = 105 := by decide
  have hch2 : (13 : ℝ) ≤ 2 * Real.logb 2 ((15 : ℕ).choose 2 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (13 : ℕ)) ≤ (((15 : ℕ).choose 2 : ℝ) ^ (2 : ℕ)) by rw [hc2]; norm_num)
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
      Nat.cast_ofNat, Nat.cast_ofNat] at hl
  have hlog1024 : Real.logb 2 ((1024 : ℕ) : ℝ) = 10 := by
    rw [Nat.cast_ofNat, show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  rw [benchmarkBits_eq, hlog1024]; push_cast at hch2 ⊢; linarith

/-- Concrete non-vacuity instantiations of all three **Word-RAM Theorem 1.3(1)–(2)** update-only
actual-expected-time headlines (`expectedFlatTime_update_ge_iterLog`,
`expectedFlatTime_update_ge_sublinear`, `expectedFlatTime_update_ge_iterLogStar_add_log_div`) and
all three certified-budget corollaries (`expectedTotalCost_update_ge_iterLog`,
`expectedTotalCost_update_ge_sublinear`, `expectedTotalCost_update_ge_iterLogStar_add_log_div`) on
deterministic `twoSlotDetImpl.toRandomized` and coin-flipping `twoSlotRandImpl` at
`(U = 15, V = 1024, n = 2, k = 1, w = 14, R = 3 / 2, α_V = 1)` with strictly positive bounds. -/
theorem wordram_theorem1_3_concrete_instantiations :
    let C_det := (twoSlotDetImpl (U := 15) (V := 1024) (w := 14) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)).toRandomized
    let C_rand := twoSlotRandImpl (U := 15) (V := 1024) (w := 14) (base := 0) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
    (∃ ν₀ : PMF (C_det.Seed × Data 9),
      let body := flatExpectedBodyTime 14
        ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
        (twoSlotDetCode 0 false).input C_det.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 15 1024 2 7, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 15 1024 2) C_det.Seed 14 0 2
          ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
          (twoSlotDetCode 0 false).input C_det.encode (fun o _ regs => C_det.decode o regs)
          (Dictionary.empty 15) ops ν₀ ν_final (body ops)) ∧
      (∃ c > 0, ENNReal.ofReal (c * 2) ≤
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops * body ops) ∧
      (∃ B > 0, ENNReal.ofReal B ≤
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops * body ops) ∧
      (∃ c > 0, ENNReal.ofReal (c * 2 * (1 + Real.logb 2 (4 / 3))) ≤
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops * body ops)) ∧
    (∃ ν₀ : PMF (C_rand.Seed × Data 9),
      let body := flatExpectedBodyTime 14
        ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
        (twoSlotRandCode 0 false).input C_rand.encode (ν₀.map Prod.snd)
      (∀ ops ∈ validHistoriesUpTo 15 1024 2 7, body ops ≠ ⊤ ∧ ∃ ν_final,
        ExecFlatProgramOps (Dynamic.spec 15 1024 2) C_rand.Seed 14 0 2
          ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
          (twoSlotRandCode 0 false).input C_rand.encode (fun o _ regs => C_rand.decode o regs)
          (Dictionary.empty 15) ops ν₀ ν_final (body ops)) ∧
      (∃ c > 0, ENNReal.ofReal (c * 2 * (Nat.logStar 2 : ℝ)) ≤
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops * body ops) ∧
      (∃ B > 0, ENNReal.ofReal B ≤
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops * body ops) ∧
      (∃ c > 0, ENNReal.ofReal (c * 2 * (1 + Real.logb 2 (4 / 3))) ≤
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops * body ops)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤ (C_det.initPotential : ℝ≥0∞) +
      ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops *
        ((Dynamic.spec 15 1024 2).totalCost C_det.charge (Dictionary.empty 15) ops : ℝ≥0∞)) ∧
    (∃ B > 0, ENNReal.ofReal B ≤ (C_rand.initPotential : ℝ≥0∞) +
      ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops *
        ((Dynamic.spec 15 1024 2).totalCost C_rand.charge (Dictionary.empty 15) ops : ℝ≥0∞)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2 * (1 + Real.logb 2 (4 / 3))) ≤
      (C_rand.initPotential : ℝ≥0∞) +
        ∑' ops, insertDeleteDist 15 1024 2 (by decide) (by decide) ops *
          ((Dynamic.spec 15 1024 2).totalCost C_rand.charge (Dictionary.empty 15) ops : ℝ≥0∞)) := by
  intro C_det C_rand
  have hp0 := (persistentRegCount_twoSlot_false 0).1
  have hpr := (persistentRegCount_twoSlot_false 0).2
  have hpc0 : persCount (twoSlotDetCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hp0]
  have hpcr : persCount (twoSlotRandCode 0 false).input = 0 := by
    rw [← persistentRegCount_eq_persCount, hpr]
  have hV_lo : (15 : ℝ) ^ ((2 : ℝ) + 1) ≤ (1024 : ℝ) * (2 : ℝ) ^ 2 := by norm_num
  have hk_hi : 1 ≤ Nat.logStar 2 := by decide
  have hls2 : Nat.logStar 2 = 1 := by decide
  have hsp_sub : (((2 + 0) * 14 : ℕ) : ℝ) ≤ benchmarkBits 15 1024 2 + (3 / 2 : ℝ) := by
    push_cast; linarith [benchmarkBits_15_1024_2_ge]
  have hsp_iter : (((2 + 0) * 14 : ℕ) : ℝ) ≤
      benchmarkBits 15 1024 2 + 1 * (2 : ℝ) * ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by
    have hmax : max (Nat.iterLog 1 2) 1 = 1 := by decide
    rw [hmax]; push_cast; linarith [benchmarkBits_15_1024_2_ge]
  have hsp_star : (((2 + 0) * 14 : ℕ) : ℝ) ≤
      benchmarkBits 15 1024 2 +
        1 * (2 : ℝ) * ((max (Nat.iterLog (Nat.logStar 2) 2) 1 : ℕ) : ℝ) := by
    have hmax : max (Nat.iterLog (Nat.logStar 2) 2) 1 = 1 := by decide
    rw [hmax]; push_cast; linarith [benchmarkBits_15_1024_2_ge]
  have hsp_det : C_det.space = 2 := rfl
  have hsp_rand : C_rand.space = 2 := rfl
  have hlog_eq : Real.logb 2 (((2 : ℕ) : ℝ) / max (3 / 2 : ℝ) 1) = Real.logb 2 (4 / 3) := by
    rw [max_eq_left (by norm_num : (1 : ℝ) ≤ 3 / 2), Nat.cast_ofNat]
    norm_num
  have hlpos : 0 < Real.logb 2 (4 / 3) := hlog_eq ▸ logb_four_thirds_pos
  obtain ⟨ν_d, hsupp_d, hreal_d, hcorr_d⟩ :=
    validHist_flatExec_of_steps (M := 7) C_det (fits_zero 14) nofun nofun nofun
  obtain ⟨ν_r, hsupp_r, hreal_r, hcorr_r⟩ :=
    validHist_flatExec_of_steps (M := 7) C_rand (fits_zero 14) nofun nofun nofun
  obtain ⟨c₁, hc₁, hf₁⟩ := expectedFlatTime_update_ge_iterLog.{0}
    (α_V := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂, hf₂⟩ := expectedFlatTime_update_ge_sublinear.{0}
    (α_V := 1) (c_w := 2) 0 (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hf₃⟩ := expectedFlatTime_update_ge_iterLogStar_add_log_div.{0}
    (α_V := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₄, hc₄, hb₁⟩ := expectedTotalCost_update_ge_iterLog
    (α_V := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₅, hc₅, hb₂⟩ := expectedTotalCost_update_ge_sublinear
    (α_V := 1) (c_w := 2) 0 (by norm_num) (by norm_num)
  obtain ⟨c₆, hc₆, hb₃⟩ := expectedTotalCost_update_ge_iterLogStar_add_log_div
    (α_V := 1) (c_R := 1) (c_w := 2) 0 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨ν_d, hreal_d,
      ⟨c₁, hc₁, ?_⟩, ⟨c₂ * 2 * Real.logb 2 (4 / 3), by positivity, ?_⟩, ⟨c₃, hc₃, ?_⟩⟩,
    ⟨ν_r, hreal_r,
      ⟨c₁, hc₁, ?_⟩, ⟨c₂ * 2 * Real.logb 2 (4 / 3), by positivity, ?_⟩, ⟨c₃, hc₃, ?_⟩⟩,
    ⟨c₄, hc₄, ?_⟩,
    ⟨c₅ * 2 * Real.logb 2 (4 / 3), by positivity, ?_⟩,
    ⟨c₆, hc₆, ?_⟩⟩
  · have h := hf₁ (by decide) (by decide) (by decide) hV_lo le_rfl hk_hi (by omega) hw_15_1024
      (by rw [hpc0]; exact hsp_iter)
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det.encode (fun o _ regs => C_det.decode o regs) ν_d hsupp_d hcorr_d
    push_cast at h; rwa [mul_one] at h
  · have h := hf₂ (R := 3 / 2) (by decide) (by decide) (by decide) hV_lo (by norm_num) (by omega)
      hw_15_1024 (by rw [hpc0]; exact hsp_sub)
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det.encode (fun o _ regs => C_det.decode o regs) ν_d hsupp_d hcorr_d
    rw [hlog_eq] at h; push_cast at h; exact h
  · have h := hf₃ (R := 3 / 2) (by decide) (by decide) (by decide) hV_lo (by norm_num) (by omega)
      hw_15_1024 (by rw [hpc0]; exact hsp_sub)
      ((twoSlotDetCode 0 false).code.program (twoSlotDetCode 0 false).output)
      C_det.encode (fun o _ regs => C_det.decode o regs) ν_d hsupp_d hcorr_d
    rw [hlog_eq, hls2, max_eq_right hlpos.le] at h; push_cast at h; exact h
  · have h := hf₁ (k := Nat.logStar 2) (by decide) (by decide) (by decide) hV_lo hk_hi le_rfl
      (by omega) hw_15_1024 (by rw [hpcr]; exact hsp_star)
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r
    push_cast at h; exact h
  · have h := hf₂ (R := 3 / 2) (by decide) (by decide) (by decide) hV_lo (by norm_num) (by omega)
      hw_15_1024 (by rw [hpcr]; exact hsp_sub)
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r
    rw [hlog_eq] at h; push_cast at h; exact h
  · have h := hf₃ (R := 3 / 2) (by decide) (by decide) (by decide) hV_lo (by norm_num) (by omega)
      hw_15_1024 (by rw [hpcr]; exact hsp_sub)
      ((twoSlotRandCode 0 false).code.program (twoSlotRandCode 0 false).output)
      C_rand.encode (fun o _ regs => C_rand.decode o regs) ν_r hsupp_r hcorr_r
    rw [hlog_eq, hls2, max_eq_right hlpos.le] at h; push_cast at h; exact h
  · have h := hb₁ (by decide) (by decide) (by decide) hV_lo le_rfl hk_hi (by omega) hw_15_1024
      C_det (by rw [hsp_det, hp0]; exact hsp_iter)
      (fits_zero 14) nofun nofun nofun
    push_cast at h; rwa [mul_one] at h
  · have h := hb₂ (R := 3 / 2) (by decide) (by decide) (by decide) hV_lo (by norm_num) (by omega)
      hw_15_1024 C_rand (by rw [hsp_rand, hpr]; exact hsp_sub)
      (fits_zero 14) nofun nofun nofun
    rw [hlog_eq] at h; push_cast at h; exact h
  · have h := hb₃ (R := 3 / 2) (by decide) (by decide) (by decide) hV_lo (by norm_num) (by omega)
      hw_15_1024 C_rand (by rw [hsp_rand, hpr]; exact hsp_sub)
      (fits_zero 14) nofun nofun nofun
    rw [hlog_eq, hls2, max_eq_right hlpos.le] at h; push_cast at h; exact h

end CslibFrontierTests.DictLowerBoundWordRAM
