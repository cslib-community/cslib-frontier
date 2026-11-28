/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.DataStructure.FenwickTree.WordRAM
import Mathlib.Algebra.Group.ULift

/-!
# Fenwick Tree Tests and Word-RAM Non-Vacuity Witnesses

Kernel-checked examples and theorems (without `native_decide`) exercising:

1. `lowbit`, unsigned bitwise `m &&& (m - 1)` / `m - (m &&& (m - 1))`, `downChain`, `upChain`, and
   `fenwickChildren` combinatorics.
2. Exact agreement between `ofList` / `ofArray` immediate-parent construction and incremental `add`
   from `zeros` (`ofList_eq_buildByAdds`), across empty (`n = 0`), singleton (`n = 1`), power-of-two
   (`n = 16`), and non-power-of-two (`n = 6, 13`) lengths, plus out-of-bounds totality.
3. `[AddCommGroup ℤ]` operations (`rangeSum`, `get`, `set`) at length `n = 7` with negative updates,
   and universe polymorphism of `FenwickTree` in `Type 1` (`ULift.{1} ℤ`).
4. Word-RAM concrete execution (`Code.eval`, `DynamicProgram.eval`), `buildCode_spec` on relocated
   memory (`base = 4`, preserving dirty sentinels outside `[4, 10)`), a maximum-address boundary
   witness at `w = 3, base = 0, n = 7 = 2 ^ 3 - 1` where `¬ Fits 3 (2 * n)` yet `buildCode_spec`,
   `impl`, `run_ops_exact_reusable_ofFn`, and adaptive `client_spec` all succeed without overflow.
5. Positive and negative `Valid` witnesses showing both conjuncts of `Valid` are non-vacuous and
   independently necessary.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.FenwickTree

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.FenwickTree
open Cslib.DataStructure.FenwickTree.WordRAM Cslib.DataStructure.FenwickTree.WordRAM.Reg

/-! ## 1. `lowbit`, bitwise identities, chain, and child-interval checks -/

example :
    lowbit 0 = 0 ∧
      lowbit 1 = 1 ∧
      lowbit 6 = 2 ∧
      lowbit 12 = 4 ∧
      lowbit 13 = 1 ∧
      lowbit 16 = 16 ∧
      (13 - (13 &&& 12) = lowbit 13) ∧
      (12 &&& 11 = 12 - lowbit 12) := by
  simp [lowbit.eq_def]

example :
    downChain 0 = [] ∧
      downChain 7 = [7, 6, 4] ∧
      downChain 13 = [13, 12, 8] ∧
      downChain 16 = [16] := by
  simp [downChain.eq_def, lowbit.eq_def]

example :
    upChain 16 0 = [] ∧
      upChain 16 1 = [1, 2, 4, 8, 16] ∧
      upChain 13 3 = [3, 4, 8] ∧
      upChain 13 14 = [] := by
  simp [upChain.eq_def, lowbit.eq_def]

example :
    fenwickChildren 8 = ({4, 6, 7} : Finset ℕ) ∧
      fenwickChildren 6 = ({5} : Finset ℕ) ∧
      fenwickChildren 5 = (∅ : Finset ℕ) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 2. Pure `ofList` vs incremental `add` and non-power-of-two sizes -/

private def addFrom {α : Type*} [AddCommMonoid α] :
    ℕ → List α → FenwickTree α → FenwickTree α
  | _, [], t => t
  | idx, x :: xs, t => addFrom (idx + 1) xs (add t idx x)

/-- Build a Fenwick tree by `n` sequential `add` calls starting from `zeros xs.length`. -/
def buildByAdds {α : Type*} [AddCommMonoid α] (xs : List α) : FenwickTree α :=
  addFrom 0 xs (zeros xs.length)

private theorem addAt_append_zero_cons {α : Type*} [AddZeroClass α]
    (pre : List α) (x : α) (rest : List α) :
    PrefixSums.addAt (pre ++ 0 :: rest) pre.length x = (pre ++ [x]) ++ rest := by
  induction pre with
  | nil =>
    simp only [PrefixSums.addAt, List.nil_append, List.length_nil, List.getD_cons_zero,
      zero_add, List.set_cons_zero, List.singleton_append]
  | cons a as ih =>
    simpa only [PrefixSums.addAt, List.cons_append, List.length_cons, List.getD_cons_succ,
      List.set_cons_succ] using congrArg (a :: ·) ih

private theorem valid_addFrom {α : Type*} [AddCommMonoid α]
    (pre suf : List α) {t : FenwickTree α}
    (hv : Valid t (pre ++ List.replicate suf.length 0)) :
    Valid (addFrom pre.length suf t) (pre ++ suf) := by
  induction suf generalizing pre t with
  | nil =>
    simpa only [addFrom, List.length_nil, List.replicate_zero, List.append_nil] using hv
  | cons x xs ih =>
    simp only [addFrom]
    have hstep := addAt_append_zero_cons pre x (List.replicate xs.length 0)
    have hv' : Valid (add t pre.length x) ((pre ++ [x]) ++ List.replicate xs.length 0) :=
      hstep ▸ valid_add hv pre.length x
    have hlen : (pre ++ [x]).length = pre.length + 1 := by
      simp only [List.length_append, List.length_singleton]
    simpa only [hlen, List.append_assoc, List.singleton_append] using ih (pre ++ [x]) hv'

/-- Canonical uniqueness corollary: immediate-parent `ofList xs` produces the exact same
`FenwickTree α` as `xs.length` incremental `add` updates on `zeros xs.length`. -/
theorem ofList_eq_buildByAdds {α : Type*} [AddCommMonoid α] (xs : List α) :
    ofList xs = buildByAdds xs := by
  apply (valid_ofList xs).unique
  simpa only [buildByAdds, List.nil_append, List.length_nil] using
    valid_addFrom ([] : List α) xs (valid_zeros _)

def sample6 : List ℕ := [3, 1, 4, 1, 5, 9]
def sample13 : List ℕ := [1, 3, 2, 5, 4, 6, 1, 2, 7, 3, 2, 4, 5]
def sample16 : List ℕ := [1, 0, 2, 1, 1, 3, 0, 4, 2, 5, 2, 2, 3, 1, 0, 2]

example :
    ofList ([] : List ℕ) = zeros 0 ∧
      ofList [42] = buildByAdds [42] ∧
      prefixSum (ofList [42]) 1 = 42 ∧
      prefixSum (ofList ([] : List ℕ)) 5 = 0 ∧
      add (zeros (α := ℕ) 0) 0 9 = zeros 0 := by
  refine ⟨ofList_nil, ofList_eq_buildByAdds _, ?_, ?_, ?_⟩
  · rw [prefixSum_eq (valid_ofList [42]) 1]; rfl
  · rw [prefixSum_eq (valid_ofList []) 5]; rfl
  · exact add_of_size_le _ 9 (by rw [size_zeros])

example :
    ofList sample6 = buildByAdds sample6 ∧
      ofList sample13 = buildByAdds sample13 ∧
      ofList sample16 = buildByAdds sample16 ∧
      (ofList sample13).size = 13 ∧
      prefixSum (ofList sample13) 0 = 0 ∧
      prefixSum (ofList sample13) 7 = 22 ∧
      prefixSum (ofList sample13) 13 = 45 ∧
      prefixSum (ofList sample13) 20 = 45 ∧
      add (ofList sample6) 6 99 = ofList sample6 := by
  refine ⟨ofList_eq_buildByAdds _, ofList_eq_buildByAdds _, ofList_eq_buildByAdds _,
    size_ofList _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prefixSum_eq (valid_ofList sample13) 0]; decide
  · rw [prefixSum_eq (valid_ofList sample13) 7]; decide
  · rw [prefixSum_eq (valid_ofList sample13) 13]; decide
  · rw [prefixSum_eq (valid_ofList sample13) 20]; decide
  · exact add_of_size_le _ 99 (by rw [size_ofList]; decide)

/-! ## 3. Signed `[AddCommGroup ℤ]` operations and universe polymorphism -/

def signedSample : List ℤ := [4, -2, 7, -5, 3, 1, -6]

example :
    let t0 := ofList signedSample
    let t1 := set (add t0 1 (-10)) 4 20
    rangeSum t0 1 5 = 3 ∧
      rangeSum t0 5 2 = 0 ∧
      get t0 2 = 7 ∧
      get t0 9 = 0 ∧
      get t1 1 = -12 ∧
      get t1 4 = 20 ∧
      rangeSum t1 1 6 = 11 ∧
      set t1 20 99 = t1 := by
  dsimp only
  have hv0 := valid_ofList signedSample
  have hv1 := valid_set (valid_add hv0 1 (-10)) 4 20
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rangeSum_eq hv0]; decide
  · rw [rangeSum_eq hv0]; decide
  · rw [get_eq hv0]; decide
  · rw [get_eq hv0]; decide
  · rw [get_eq hv1]; decide
  · rw [get_eq hv1]; decide
  · rw [rangeSum_eq hv1]; decide
  · exact set_of_size_le _ 99 (by simp [signedSample])

example :
    let s : List (ULift.{1} ℤ) := [⟨3⟩, ⟨-1⟩, ⟨5⟩]
    Valid (ofList s) s ∧
      prefixSum (ofList s) 2 = ⟨2⟩ ∧
      rangeSum (ofList s) 1 3 = ⟨4⟩ := by
  intro s
  have hv := valid_ofList s
  refine ⟨hv, ?_, ?_⟩
  · rw [prefixSum_eq hv]; rfl
  · rw [rangeSum_eq hv]; rfl

/-! ## 4. Word-RAM concrete execution, boundary witness, and adaptive client checks -/

/-- Relocated initial state at `base = 4, w = 6` holding `sample6 = [3, 1, 4, 1, 5, 9]` in
`[4, 10)` and dirty sentinels `61` at `3` and `57` at `10`. -/
def rawData6 : Data 12 where
  regs i := if i = rBase then 4 else if i = rLen then 6 else if i = rFrontier then 10 else 0
  mem a :=
    if a = 3 then 61
    else if a = 10 then 57
    else if 4 ≤ a ∧ a < 10 then sample6.getD (a - 4) 0
    else 0

theorem bounded_rawData6 : rawData6.Bounded 6 := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · fin_cases i <;> decide
  · simp only [rawData6]
    split_ifs with h3 h10 hrange
    · decide
    · decide
    · have hcases : a - 4 = 0 ∨ a - 4 = 1 ∨ a - 4 = 2 ∨ a - 4 = 3 ∨ a - 4 = 4 ∨ a - 4 = 5 := by
        omega
      rcases hcases with h | h | h | h | h | h <;> rw [h] <;> decide
    · decide

-- Concrete `Code.eval` execution of `buildCode` on `rawData6`: transforms `[3, 1, 4, 1, 5, 9]`
-- in-place into Fenwick cells `[3, 4, 4, 9, 5, 14]`, preserves sentinels `61` and `57`, and runs
-- within the `17 * 6 + 5 = 107` bound.
private theorem builtPair6_isSome : (buildCode.eval 6 10 rawData6).isSome = true := by
  decide +kernel

private abbrev builtPair6 : Data 12 × ℕ :=
  (buildCode.eval 6 10 rawData6).get builtPair6_isSome

example :
    ∃ y steps, buildCode.eval 6 10 rawData6 = some (y, steps) ∧
      steps ≤ 17 * sample6.length + 5 ∧
      y.mem 3 = 61 ∧
      y.mem 10 = 57 ∧
      [y.mem 4, y.mem 5, y.mem 6, y.mem 7, y.mem 8, y.mem 9] = [3, 4, 4, 9, 5, 14] := by
  refine ⟨builtPair6.1, builtPair6.2, (Option.some_get builtPair6_isSome).symm, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

-- Concrete `DynamicProgram.eval` execution of `add` and `sum` (including clamped `sum 9`)
-- after building from `rawData6`.
private abbrev testProg6 :=
  (implStandard (by decide : 0 < 6) (by decide : Fits 6 (4 + 6))).toDynamicProgram
    (recoding (by decide : 0 < 6) (by decide : Fits 6 (4 + 6)))

private theorem evalStep1_isSome :
    (testProg6.eval 6 10 (.sum 3) builtPair6.1).isSome = true := by decide +kernel

private abbrev evalStep1 : Data 12 × ℕ × ℕ :=
  (testProg6.eval 6 10 (.sum 3) builtPair6.1).get evalStep1_isSome

private theorem evalStep2_isSome :
    (testProg6.eval 6 10 (.add 4 10) evalStep1.1).isSome = true := by decide +kernel

private abbrev evalStep2 : Data 12 × Unit × ℕ :=
  (testProg6.eval 6 10 (.add 4 10) evalStep1.1).get evalStep2_isSome

private theorem evalStep3_isSome :
    (testProg6.eval 6 10 (.sum 9) evalStep2.1).isSome = true := by decide +kernel

private abbrev evalStep3 : Data 12 × ℕ × ℕ :=
  (testProg6.eval 6 10 (.sum 9) evalStep2.1).get evalStep3_isSome

example :
    ∃ y1 c1 y2 c2 y3 c3,
      testProg6.eval 6 10 (.sum 3) builtPair6.1 = some (y1, 8, c1) ∧
      testProg6.eval 6 10 (.add 4 10) y1 = some (y2, (), c2) ∧
      testProg6.eval 6 10 (.sum 9) y2 = some (y3, 33, c3) ∧
      c1 ≤ 13 * Nat.clog 2 (6 + 1) + 12 ∧
      c2 ≤ 13 * Nat.clog 2 (6 + 1) + 12 ∧
      c3 ≤ 13 * Nat.clog 2 (6 + 1) + 12 := by
  have ha1 : evalStep1.2.1 = 8 := by decide +kernel
  have ha3 : evalStep3.2.1 = 33 := by decide +kernel
  refine ⟨evalStep1.1, evalStep1.2.2, evalStep2.1, evalStep2.2.2, evalStep3.1, evalStep3.2.2,
    ?_, (Option.some_get evalStep2_isSome).symm, ?_, ?_, ?_, ?_⟩
  · rw [← ha1]; exact (Option.some_get evalStep1_isSome).symm
  · rw [← ha3]; exact (Option.some_get evalStep3_isSome).symm
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Maximum-address boundary witness at `w = 3, base = 0, n = 7 = 2 ^ 3 - 1`: `Fits 3 (0 + 7)`
holds while `¬ Fits 3 (2 * 7)`, exercising overflow-free `n - m < lowbit m` parent bounds in
`buildCode_spec`, `impl`, `run_ops_exact_reusable_ofFn`, and adaptive `client_spec`. -/
def boundaryList7 : List ℕ := [1, 1, 0, 1, 1, 0, 1]

def rawData7 : Data 12 where
  regs i := if i = rLen then 7 else 0
  mem a := if a < 7 then boundaryList7.getD a 0 else 0

theorem bounded_rawData7 : rawData7.Bounded 3 := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · fin_cases i <;> decide
  · simp only [rawData7]
    split_ifs with ha
    · have hcases : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · decide

/-- Adaptive client: query `sum 4`; if at least `3`, add `2` at index `2`, else add `1` at
index `0`; then return `(s4, sum 7)`. -/
def adaptiveWordClient (w : ℕ) : (WordRAM.spec w).Client (ℕ × ℕ) :=
  .liftBind (.sum 4) fun s4 =>
    .liftBind (if 3 ≤ s4 then .add 2 2 else .add 0 1) fun _ =>
      .liftBind (.sum 7) fun s7 =>
        .pure (s4, s7)

-- End-to-end non-vacuity witness at `w = 3, base = 0, n = 7` (`¬ Fits 3 (2 * 7)`):
-- `buildCode_spec` constructs `Rep 0 7 3 boundaryList7 y` in `≤ 124` instructions, and
-- `client_spec` executes `adaptiveWordClient 3` returning `(3, 7)` within `3 * (13 * 3 + 12)`
-- instructions.
example :
    Fits 3 (0 + boundaryList7.length) ∧
      ¬ Fits 3 (2 * boundaryList7.length) ∧
      ∃ y z traces,
        ExecWithin 3 buildCode rawData7 y (17 * boundaryList7.length + 5) ∧
        Rep 0 boundaryList7.length 3 boundaryList7 y ∧
        Executes
          (((implStandard (by decide : 0 < 3) (by decide : Fits 3 (0 + 7))).toDynamicProgram
            (recoding (by decide : 0 < 3) (by decide : Fits 3 (0 + 7)))).ExecOp 3)
          (adaptiveWordClient 3) y (3, 7) z traces ∧
        total DynamicProgram.OperationTrace.instructions traces ≤
          3 * (13 * Nat.clog 2 (boundaryList7.length + 1) + 12) := by
  have hw : 0 < 3 := by decide
  have hf : Fits 3 (0 + boundaryList7.length) := by decide
  have hnf : ¬ Fits 3 (2 * boundaryList7.length) := by decide
  have hsum : Fits 3 boundaryList7.sum := by decide
  obtain ⟨y, hexec, hrep, _, _, _⟩ :=
    buildCode_spec hw hf hsum bounded_rawData7 rfl rfl fun i hi => by
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
        simp only [boundaryList7, List.length_cons, List.length_nil] at hi
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hhist :
      (WordRAM.spec 3).clientHistory boundaryList7 (adaptiveWordClient 3) =
        [.sum 4, .add 2 2, .sum 7] := by decide
  have hv_hist :
      (WordRAM.spec 3).ValidHistory boundaryList7
        ((WordRAM.spec 3).clientHistory boundaryList7 (adaptiveWordClient 3)) := by
    rw [hhist]
    simp [StateTransitionSpec.ValidHistory, WordRAM.spec, WordRAM.valid,
      PrefixSums.step, boundaryList7, Fits]
  have hres :
      (WordRAM.spec 3).clientResult boundaryList7 (adaptiveWordClient 3) = (3, 7) := by
    decide
  have hlen_hist :
      ((WordRAM.spec 3).clientHistory boundaryList7 (adaptiveWordClient 3)).length = 3 := by
    rw [hhist]
    rfl
  obtain ⟨z, traces, hclient, _, htot⟩ := client_spec hw hf (adaptiveWordClient 3) hrep hv_hist
  rw [hres] at hclient
  rw [hlen_hist] at htot
  exact ⟨hf, hnf, y, z, traces, hexec, hrep, hclient, htot⟩

-- Standalone flat-program sequence non-vacuity (`run_ops_exact_reusable_ofFn` on dirty memory):
example :
    let hw : 0 < 3 := by decide
    let hf : Fits 3 (0 + 7) := by decide
    let ops : List (PrefixSums.Op ℕ) := [.add 0 3, .add 5 4, .sum 6]
    ∃ pc₀ x₀ t_init z t_ops,
      Runs 3 subroutineCode.initClearProg ⟨0, rawData7⟩ ⟨pc₀, x₀⟩ t_init ∧
      t_init ≤ (impl hw hf).initTime + 4 * 7 + 6 ∧
      (impl hw hf).RunsOps (impl hw hf).prepareRegs (List.replicate 7 0) x₀ ops
        ((WordRAM.spec 3).canonicalTranscript (List.replicate 7 0) ops)
        ((WordRAM.spec 3).run (List.replicate 7 0) ops).1 z t_ops := by
  have hw : 0 < 3 := by decide
  have hf : Fits 3 (0 + 7) := by decide
  let ops : List (PrefixSums.Op ℕ) := [.add 0 3, .add 5 4, .sum 6]
  have hv : (WordRAM.spec 3).ValidHistory (List.replicate 7 0) ops := by
    simp [StateTransitionSpec.ValidHistory, WordRAM.spec, WordRAM.valid, ops,
      PrefixSums.step, PrefixSums.addAt, Fits]
  obtain ⟨pc₀, x₀, t_init, z, t_ops, hruns₀, _, _, hruns_ops, _, ht_init, _⟩ :=
    (impl hw hf).run_ops_exact_reusable_ofFn bounded_rawData7 rfl
      (fun j => by fin_cases j; rfl) ops hv
  exact ⟨pc₀, x₀, t_init, z, t_ops, hruns₀, ht_init, hruns_ops⟩

/-! ## 5. Positive and negative `Valid` witnesses -/

theorem valid_manual4 : Valid (⟨#[3, 4, 4, 9]⟩ : FenwickTree ℕ) [3, 1, 4, 1] := by
  refine ⟨rfl, fun m hm1 hm4 => ?_⟩
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
    change m ≤ 4 at hm4
    omega
  rcases hm_cases with rfl | rfl | rfl | rfl <;>
    simp [lowbit.eq_def]

example : ofList [3, 1, 4, 1] = ⟨#[3, 4, 4, 9]⟩ :=
  (valid_ofList [3, 1, 4, 1]).unique valid_manual4

example : ¬ Valid (⟨#[3, 4, 4]⟩ : FenwickTree ℕ) [3, 1, 4, 1] := by
  intro hv
  have h : (3 : ℕ) = 4 := hv.1
  omega

example : ¬ Valid (⟨#[3, 4, 4, 8]⟩ : FenwickTree ℕ) [3, 1, 4, 1] := by
  intro hv
  have h4 := hv.2 4 (by omega) (by decide)
  have hlhs : (⟨#[3, 4, 4, 8]⟩ : FenwickTree ℕ).tree[4 - 1] = 8 := rfl
  have hrhs : (([3, 1, 4, 1].take 4).drop (4 - lowbit 4)).sum = 9 := by simp [lowbit.eq_def]
  rw [hlhs, hrhs] at h4
  omega

end CslibFrontierTests.FenwickTree
