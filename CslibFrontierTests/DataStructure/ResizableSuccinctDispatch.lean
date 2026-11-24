/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test)

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch

public section

open Cslib
open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.Probability

/-!
# Unit and Soundness Tests for In-Epoch Resizable Succinct Dispatch

This test suite covers:
1. Register layout and distinctness for parameter-free operational dispatch (Test 1).
2. Width-independence (`¬inEpochOpCode.ReadsWidth`) and exchange-factor positivity (Test 2).
3. Concrete non-vacuous execution (`inEpochOpCode_execRCodeDist`, `inEpochOpCode_peakFrontierLe`)
   across sequential `init → query → delete` transitions and active-epoch `InEpochValid` instances
   for `query`, `insert`, and `delete` (Test 3).
4. `.halt` / no-op rejection soundness tests verifying that a no-op stub cannot preserve
   `CompactedRep` across item-stream growth (Test 4).
-/

/-! ### Test 1: Register layout and distinctness -/

theorem test_rEpoch_lower_bound : 88 ≤ rEpoch := le_rEpoch

theorem test_registers_distinct :
    rBase ≠ rFr ∧ rFr ≠ rTag ∧ rTag ≠ rArgU ∧ rArgU ≠ rArgV ∧
    rArgV ≠ rOutTag ∧ rOutTag ≠ rOutVal :=
  ⟨eReg_ne (by decide), eReg_ne (by decide), eReg_ne (by decide),
   eReg_ne (by decide), eReg_ne (by decide), eReg_ne (by decide)⟩

theorem test_grow_shrink_nodup :
    ([rK, rRes, rCur, rIdx, rZero, rOne] : List (Fin rEpoch)).Nodup ∧
    ([rK, rIdx, rZero, rOne] : List (Fin rEpoch)).Nodup :=
  ⟨rGrow_nodup, rShrink_nodup⟩

/-! ### Test 2: Parameter-free `¬ReadsWidth` and factor positivity -/

theorem test_inEpochOpCode_not_readsWidth : ¬inEpochOpCode.ReadsWidth :=
  not_readsWidth_inEpochOpCode

theorem test_inEpochFactor_pos : 1 ≤ inEpochFactor :=
  one_le_inEpochFactor

/-! ### Test 3: Concrete execution, `PeakFrontierLe`, and active-epoch non-vacuity -/

/-- Concrete memory layout for an empty initial resting dictionary state (`U = 64, V = 2 ^ 64,
w = 64, N = 0, n = 0`). -/
def testEmptyMem (a : ℕ) : ℕ :=
  if a = 0 then 63
  else if a = 1 then 2 ^ 64 - 1
  else if a = 2 then 64
  else if a = 3 then keyBits 64
  else if a = 4 then valBits (2 ^ 64)
  else 0

/-- Empty initial machine state encoded for `o : Dynamic.Op 64` at `base = 0`. -/
@[expose]
noncomputable def testEmptyStateFor (o : Dynamic.Op 64) : RData rEpoch :=
  ⟨encode o, testEmptyMem, 8⟩

theorem testEmptyStateFor_bounded (o : Dynamic.Op 64)
    (ho : ∀ r, Fits 64 (encode o r)) : (testEmptyStateFor o).Bounded 64 := by
  refine ⟨⟨ho, ?_⟩, show Fits 64 8 by decide, ?_⟩
  · intro a
    change testEmptyMem a < 2 ^ 64
    unfold testEmptyMem
    split_ifs <;> decide
  · intro a ha
    change 8 ≤ a at ha
    change testEmptyMem a = 0
    unfold testEmptyMem
    have : a ≠ 0 := by omega
    have : a ≠ 1 := by omega
    have : a ≠ 2 := by omega
    have : a ≠ 3 := by omega
    have : a ≠ 4 := by omega
    simp only [*, ↓reduceIte]

theorem test_rootHeader_empty (o : Dynamic.Op 64) :
    RootHeaderValid 64 (2 ^ 64) 64 0 0 0 0 (testEmptyStateFor o).mem := by
  dsimp only [testEmptyStateFor, testEmptyMem]
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

theorem test_compactedRep_empty (o : Dynamic.Op 64) (ho : ∀ r, Fits 64 (encode o r)) :
    CompactedRep 64 (2 ^ 64) 64 0 0 0 0 (Dictionary.empty 64) (testEmptyStateFor o) :=
  compactedRep_empty (testEmptyStateFor_bounded o ho) rfl (test_rootHeader_empty o)

/-- Test 3a: Sequential execution `init → query → delete` on the Resizable Word RAM via
`inEpochOpCode_execRCodeDist` and `inEpochOpCode_peakFrontierLe`. -/
theorem test_sequential_query_then_delete :
    let k5 : Fin 64 := ⟨5, by decide⟩
    let o_q : Dynamic.Op 64 := .query k5
    let o_d : Dynamic.Op 64 := .delete k5
    let x₀ := testEmptyStateFor o_q
    PeakFrontierLe 64 (0 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64 0)
      (inEpochOpCode.program rOutTag) ⟨0, x₀⟩ ∧
    ∃ (y₁ y₂ : RData rEpoch) (steps₁ steps₂ : ℕ),
      ExecRCodeDist 64 inEpochOpCode x₀ (PMF.pure y₁) steps₁
        (0 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64 0) ∧
      decode o_q y₁.regs = some none ∧
      CompactedRep 64 (2 ^ 64) 64 0 0 0 0 (Dictionary.empty 64) y₁ ∧
      ExecRCodeDist 64 inEpochOpCode
        { regs := encode o_d, mem := y₁.mem, frontier := y₁.frontier }
        (PMF.pure y₂) steps₂
        (0 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64 0) ∧
      decode o_d y₂.regs = some () ∧
      CompactedRep 64 (2 ^ 64) 64 0 0 0 0 (Dictionary.empty 64) y₂ := by
  intro k5 o_q o_d x₀
  have hfit_q : ∀ r, Fits 64 (encode o_q r) := fun r => by
    dsimp only [o_q, encode, Fits]; split_ifs <;> decide
  have hrep₀ := test_compactedRep_empty o_q hfit_q
  have hcard_empty : (Dictionary.dom (Dictionary.empty 64)).card = 0 := by
    rw [Dictionary.dom_empty, Finset.card_empty]
  have hval_q : InEpochValid (2 ^ 64) 0 (Dictionary.empty 64) o_q :=
    ⟨trivial, Or.inl ⟨hcard_empty, rfl⟩⟩
  have hbase_q : x₀.regs rBase = 0 := by
    dsimp only [x₀, testEmptyStateFor, o_q, encode]
    rw [ite_eq_right (eReg_ne (by decide)), ite_eq_right (eReg_ne (by decide))]
  have hpeak_q : Fits 64 (0 + inEpochPeakWords (2 ^ 64) 64 0 0 (Dictionary.empty 64) o_q) := by
    change Fits 64 (0 + compactedEpochWords 64 (2 ^ 64) 64 0
      (max 0 (Dictionary.dom (Dictionary.empty 64)).card))
    rw [hcard_empty, max_self]
    decide
  have hpf := inEpochOpCode_peakFrontierLe o_q hrep₀ hval_q hbase_q (argMatch_encode o_q) hpeak_q
  obtain ⟨y₁, steps₁, hex₁, hdec₁, hrep₁, _, _⟩ :=
    inEpochOpCode_execRCodeDist o_q hrep₀ hval_q hbase_q (argMatch_encode o_q) hpeak_q
  change PeakFrontierLe 64
    (0 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64
      (max 0 (Dictionary.dom (Dictionary.empty 64)).card)) _ _ at hpf
  change ExecRCodeDist 64 inEpochOpCode x₀ (PMF.pure y₁) steps₁
    (0 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64
      (max 0 (Dictionary.dom (Dictionary.empty 64)).card)) at hex₁
  change CompactedRep 64 (2 ^ 64) 64 0 (Dictionary.dom (Dictionary.empty 64)).card 0 0
    (Dictionary.empty 64) y₁ at hrep₁
  rw [hcard_empty, max_self] at hpf hex₁
  rw [hcard_empty] at hrep₁
  have hfit_d : ∀ r, Fits 64 (encode o_d r) := fun r => by
    dsimp only [o_d, encode, Fits]; split_ifs <;> decide
  set x₁' : RData rEpoch := { regs := encode o_d, mem := y₁.mem, frontier := y₁.frontier }
  have hx₁'_bdd : x₁'.Bounded 64 :=
    ⟨⟨hfit_d, hrep₁.bounded.mem_fits⟩, hrep₁.bounded.frontier_fits,
      fun a ha => hrep₁.bounded.zero_above ha⟩
  have hrep₁' : CompactedRep 64 (2 ^ 64) 64 0 0 0 0 (Dictionary.empty 64) x₁' :=
    compactedRep_empty hx₁'_bdd hrep₁.frontier_eq hrep₁.root_hdr
  have hempty : Function.update (Dictionary.empty 64) k5 none = Dictionary.empty 64 := by
    funext k; by_cases hk : k = k5 <;> [subst hk; skip] <;> simp [Dictionary.empty, *]
  have hval_d : InEpochValid (2 ^ 64) 0 (Dictionary.empty 64) o_d := by
    refine ⟨trivial, Or.inl ⟨?_, rfl⟩⟩
    change (Dictionary.dom (Function.update (Dictionary.empty 64) k5 none)).card = 0
    rw [hempty, hcard_empty]
  have hbase_d : x₁'.regs rBase = 0 := by
    dsimp only [x₁', o_d, encode]
    rw [ite_eq_right (eReg_ne (by decide)), ite_eq_right (eReg_ne (by decide))]
  have hpeak_d : Fits 64 (0 + inEpochPeakWords (2 ^ 64) 64 0 0 (Dictionary.empty 64) o_d) := by
    change Fits 64 (0 + compactedEpochWords 64 (2 ^ 64) 64 0
      (max 0 (Dictionary.dom (Function.update (Dictionary.empty 64) k5 none)).card))
    rw [hempty, hcard_empty, max_self]
    decide
  obtain ⟨y₂, steps₂, hex₂, hdec₂, hrep₂, _, _⟩ :=
    inEpochOpCode_execRCodeDist o_d hrep₁' hval_d hbase_d (argMatch_encode o_d) hpeak_d
  change CompactedRep 64 (2 ^ 64) 64 0
    (Dictionary.dom (Function.update (Dictionary.empty 64) k5 none)).card 0 0
    (Function.update (Dictionary.empty 64) k5 none) y₂ at hrep₂
  change ExecRCodeDist 64 inEpochOpCode x₁' (PMF.pure y₂) steps₂
    (0 + Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64
      (max 0 (Dictionary.dom (Function.update (Dictionary.empty 64) k5 none)).card)) at hex₂
  rw [hempty, hcard_empty, max_self] at hex₂
  rw [hempty, hcard_empty] at hrep₂
  exact ⟨hpf, y₁, y₂, steps₁, steps₂, hex₁, hdec₁, hrep₁, hex₂, hdec₂, hrep₂⟩

/-- Concrete 2-element dictionary state on `Fin 64` for active-epoch (`N = 4, n = 2`) checks. -/
def testActiveDict : Dictionary.State 64 :=
  Function.update (Function.update (Dictionary.empty 64) ⟨1, by decide⟩ (some 10))
    ⟨2, by decide⟩ (some 20)

theorem testActiveDict_card : (Dictionary.dom testActiveDict).card = 2 := by
  decide

/-- Test 3b: Non-vacuity check that `EpochValid 64 2 4` and `InEpochValid (2 ^ 64) 4 testActiveDict`
hold simultaneously for active-epoch `.query`, miss `.insert` (`2 → 3`), and hit `.delete`
(`2 → 1`), with `inEpochPeakWords` bounded by `1 · OPT` `Dynamic.succinctWords`. -/
theorem test_active_inEpochValid_all_ops :
    let o_q : Dynamic.Op 64 := .query ⟨1, by decide⟩
    let o_i : Dynamic.Op 64 := .insert ⟨3, by decide⟩ 30
    let o_d : Dynamic.Op 64 := .delete ⟨2, by decide⟩
    EpochValid 64 2 4 ∧
    InEpochValid (2 ^ 64) 4 testActiveDict o_q ∧
    InEpochValid (2 ^ 64) 4 testActiveDict o_i ∧
    InEpochValid (2 ^ 64) 4 testActiveDict o_d ∧
    inEpochPeakWords (2 ^ 64) 64 4 2 testActiveDict o_i ≤
      Dynamic.succinctWords 1355 441 64 (2 ^ 64) 64 3 := by
  intro o_q o_i o_d
  have hev : EpochValid 64 2 4 := Or.inr ⟨by decide, by decide, by decide, by decide⟩
  have hv_q : InEpochValid (2 ^ 64) 4 testActiveDict o_q := by
    refine ⟨trivial, ?_⟩
    change EpochValid 64 (Dictionary.dom testActiveDict).card 4
    rw [testActiveDict_card]
    exact hev
  have hcard_i :
      (Dictionary.dom ((Dynamic.spec 64 (2 ^ 64) 64).stepFn testActiveDict o_i).1).card = 3 := by
    decide
  have hv_i : InEpochValid (2 ^ 64) 4 testActiveDict o_i :=
    ⟨⟨Or.inl (by rw [testActiveDict_card]; decide), by decide⟩,
     by rw [hcard_i]; exact Or.inr ⟨by decide, by decide, by decide, by decide⟩⟩
  have hcard_d :
      (Dictionary.dom ((Dynamic.spec 64 (2 ^ 64) 64).stepFn testActiveDict o_d).1).card = 1 := by
    decide
  have hv_d : InEpochValid (2 ^ 64) 4 testActiveDict o_d :=
    ⟨trivial, by rw [hcard_d]; exact Or.inr ⟨by decide, by decide, by decide, by decide⟩⟩
  have hpeak := inEpochPeakWords_le_succinctWords
    (by decide : 0 < 64) (by decide : Fits 64 64) (by decide : 0 < 64) (by decide : 0 < 2 ^ 64)
    hev hv_i
  rw [hcard_i, show max 2 3 = 3 from by decide] at hpeak
  exact ⟨hev, hv_q, hv_i, hv_d, hpeak⟩

/-! ### Test 4: `.halt` / no-op rejection soundness tests -/

/-- Test 4a: Updating only a register leaves `frontier` unchanged and cannot grow memory. -/
theorem test_halt_cannot_grow {r : ℕ} (dst : Fin r) (x : RData r)
    (h_frontier : x.frontier + 1 ≠ x.frontier) :
    x.frontier + 1 ≠ (x.set dst x.frontier).frontier := by
  rw [RData.set_frontier]
  exact h_frontier

/-- Test 4b: A `.halt` / no-op program leaving `x.frontier` unchanged is rejected by `CompactedRep`
across an active miss insertion `(N = 4, n = 2 → 3)` because `compactedEpochWords` grows. -/
theorem test_noop_rejected_by_active_insert (x y : RData rEpoch)
    (s_abs s_abs' : Dictionary.State 64) (n_init base : ℕ)
    (hrep : CompactedRep 64 (2 ^ 64) 64 4 2 n_init base s_abs x)
    (hnoop : y.frontier = x.frontier) :
    ¬CompactedRep 64 (2 ^ 64) 64 4 3 n_init base s_abs' y := by
  intro hrep'
  have hgrow : compactedEpochWords 64 (2 ^ 64) 64 4 2 < compactedEpochWords 64 (2 ^ 64) 64 4 3 := by
    unfold compactedEpochWords compactedItemWords
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hq : 0 ≤ quotientBits 64 4 := Nat.zero_le _
    have hv : valBits (2 ^ 64) = 64 := by decide
    omega
  have h1 := hrep.frontier_eq
  have h2 := hrep'.frontier_eq
  omega

end
